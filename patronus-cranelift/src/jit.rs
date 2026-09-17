// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
mod bv_codegen;
mod compiler;
mod expr_graph;
mod heap;
mod runtime;
mod slot;

use baa::*;
use compiler::*;
use cranelift::module::ModuleError;
use fixedbitset::FixedBitSet;
use patronus::expr::{self, *};
use patronus::system::*;
use rustc_hash::{FxHashMap, FxHashSet};
use slot::*;
use std::cell::{Cell, RefCell};
use std::sync::LazyLock;

type JITResult<T> = Result<T, JITError>;

#[derive(Debug)]
pub enum JITError {
    /// box here due to large size of ModuleError
    CompileError(Box<ModuleError>),
}

impl From<ModuleError> for JITError {
    fn from(value: ModuleError) -> Self {
        Self::CompileError(Box::new(value))
    }
}

/// Bit vector with width less than `THIN_BV_MAX_WIDTH` is stored as Rust primitive type.
/// Otherwise, it is stored as `baa::BitVecValue`
const THIN_BV_MAX_WIDTH: u32 = 64;
/// Minimum dirty percentage of output states that will trigger batched update mode
const BATCHED_UPDATE_THRESHOLD: f64 = 0.6;
/// Only when this environment variable is set and the threshold condition is met, dynamic mode switch will be turned on.
static DYNAMIC_MODE_SWITCH: LazyLock<bool> =
    LazyLock::new(|| std::env::var("DYNAMIC_MODE_SWITCH").is_ok_and(|enable| enable.eq("1")));
/// Extra cranelift settings that will be directly passed to JIT compiler.
/// This should be a colon separated key value pair joined by comma.
static CRANELIFT_FLAGS: LazyLock<Option<String>> =
    LazyLock::new(|| std::env::var("CRANELIFT_FLAGS").ok());
/// Minimum number of expr nodes that will enable dynamic switching between per-expr and batched update mode.
/// If the number of expr nodes is less than or equal to this, JIT will always use batched update mode.
/// TODO: better heuristics than simple expr nodes count
const DYNAMIC_MODE_SWITCH_THRESHOLD: usize = 1500;

enum DirtyUpdatePolicy {
    Sparse,
    Batched,
}
struct DirtyStateRegistry {
    states: FixedBitSet,
    /// Currently used in `mark_dirty_states` to store the dirty states for next step to avoid heap allocation
    scratch_states: FixedBitSet,
    num_total_states: f64,
}

impl DirtyStateRegistry {
    fn new(init_states: FixedBitSet, num_total_states: usize) -> Self {
        Self {
            states: init_states.clone(),
            scratch_states: FixedBitSet::with_capacity(num_total_states),
            num_total_states: num_total_states as f64,
        }
    }

    #[inline]
    fn register(&mut self, dirty_states: &FixedBitSet) {
        self.states.union_with(dirty_states);
    }

    fn select_update_policy(&self) -> DirtyUpdatePolicy {
        if self.dirty_percentage() >= BATCHED_UPDATE_THRESHOLD {
            DirtyUpdatePolicy::Batched
        } else {
            DirtyUpdatePolicy::Sparse
        }
    }

    #[inline]
    fn dirty_percentage(&self) -> f64 {
        (self.states.count_ones(..) as f64) / self.num_total_states
    }
}

pub struct JITEngine<'expr> {
    input_state_buffer: StateBuffer<'expr>,
    output_state_buffer: StateBuffer<'expr>,
    /// Value placeholders for output expressions, including `output`, `bad` and `constraint`
    output_ledge: RefCell<ExprLedge>,
    output_exprs: Vec<ExprRef>,
    ctx: &'expr expr::Context,
    sys: &'expr TransitionSystem,
    /// Interior mutability for lazy compilation triggered by `Simulator::get`
    backend: RefCell<JITBackend>,
    /// For each leaf state, tracks all root state expr that transitively depends on it
    upstream_dependents: FxHashMap<ExprRef, FixedBitSet>,
    /// Maintains set of states that need to be recomputed at next step
    dirty_registry: DirtyStateRegistry,
    step_count: u64,
    /// Whether dynamic switching is enabled is determined by the number of expr nodes.
    /// When enabled, JIT will switch between per-expr and batched update mode in each `step()` according to the dirty
    /// percetange of output states.
    dynamic_update_mode_switching_enabled: bool,
    snapshots: Vec<StateBuffer<'expr>>,
    output_up_to_date: Cell<bool>,
}

struct JITBackend {
    compiler: JITCompiler,
    compiled_transition_sys: Option<EvalBatchedExprWithUpdate>,
    compiled_expr_eval: FxHashMap<ExprRef, EvalBatchedExprWithUpdate>,
    compiled_output_exprs_batched_update: Option<EvalBatchedExprWithUpdate>,
}

impl JITBackend {
    fn with_compiler_flags(flags: Option<&str>) -> Self {
        Self {
            compiler: JITCompiler::new(flags),
            compiled_transition_sys: None,
            compiled_expr_eval: FxHashMap::default(),
            compiled_output_exprs_batched_update: None,
        }
    }

    fn eval_expr_with_output_slot(
        &mut self,
        expr: ExprRef,
        ctx: &expr::Context,
        input_state_buffer: &StateBuffer<'_>,
        mut entry: SlotEntry<'_>,
    ) {
        let eval_fn = self.compiled_expr_eval.entry(expr).or_insert_with(|| {
            self.compiler
                .compile_batched_expr_eval(
                    ctx,
                    &[expr],
                    input_state_buffer,
                    &mut ExprLedge::new_singleton(ctx, expr),
                )
                .unwrap_or_else(|err| panic!("fail to compile: `{:?}` due to {:?}", ctx[expr], err))
        });
        // SAFETY: jit compiler has not been dropped
        unsafe {
            eval_fn.call(
                input_state_buffer.ledge.as_raw_data_slice(),
                std::slice::from_mut(entry.raw_data_mut()),
            );
        }
    }

    fn eval_expr(
        &mut self,
        expr: ExprRef,
        ctx: &expr::Context,
        input_state_buffer: &StateBuffer<'_>,
    ) -> SlotData {
        let mut ledge = ExprLedge::new_singleton(ctx, expr);
        self.eval_expr_with_output_slot(expr, ctx, input_state_buffer, ledge.entry_at_offset(0));
        ledge.into_slot_data().into_iter().next().unwrap()
    }

    fn batched_eval_output_exprs(
        &mut self,
        ctx: &expr::Context,
        output_exprs: &[ExprRef],
        input_state_buffer: &StateBuffer<'_>,
        output_ledge: &mut ExprLedge,
    ) {
        let eval_fn = self
            .compiled_output_exprs_batched_update
            .get_or_insert_with(|| {
                self.compiler
                    .compile_batched_expr_eval(ctx, output_exprs, input_state_buffer, output_ledge)
                    .unwrap_or_else(|err| {
                        panic!("fail to compiled batched output exprs update, due to {err:?}")
                    })
            });
        unsafe {
            eval_fn.call(
                input_state_buffer.ledge.as_raw_data_slice(),
                output_ledge.as_mut_raw_data_slice(),
            )
        }
    }

    fn step_transition_sys(
        &mut self,
        ctx: &expr::Context,
        sys: &TransitionSystem,
        input_state_buffer: &StateBuffer<'_>,
        output_state_buffer: &mut StateBuffer<'_>,
    ) {
        let eval_fn = self.compiled_transition_sys.get_or_insert_with(|| {
            self.compiler
                .compile_transition_sys(ctx, sys, input_state_buffer, &*output_state_buffer)
                .unwrap_or_else(|err| {
                    panic!("fail to compile transition step function, due to {err:?}")
                })
        });

        // SAFETY: jit compiler has not been dropped
        unsafe {
            eval_fn.call(
                input_state_buffer.ledge.as_raw_data_slice(),
                output_state_buffer.ledge.as_mut_raw_data_slice(),
            )
        }
    }
}

impl<'expr> JITEngine<'expr> {
    pub fn new(ctx: &'expr expr::Context, sys: &'expr TransitionSystem) -> JITEngine<'expr> {
        let (input_state_buffer, output_state_buffer) = slot::build_in_out_state_buffer(ctx, sys);

        let output_exprs: Vec<_> = Vec::from_iter(
            sys.outputs
                .iter()
                .map(|out| out.expr)
                .chain(sys.bad_states.iter().chain(&sys.constraints).copied())
                .collect::<FxHashSet<_>>(),
        );
        let mut output_exprs_to_offset = FxHashMap::default();
        for (idx, &expr) in output_exprs.iter().enumerate() {
            output_exprs_to_offset.insert(expr, idx);
        }
        let output_ledge = ExprLedge::new(ctx, &output_exprs, move |e| {
            output_exprs_to_offset.get(&e).copied()
        });

        let num_mutable_states = sys.states.len();
        let mut init_states = FixedBitSet::with_capacity(num_mutable_states);
        init_states.insert_range(..);
        let dirty_registry = DirtyStateRegistry::new(init_states, num_mutable_states);
        let dynamic_update_mode_switching_enabled =
            *DYNAMIC_MODE_SWITCH && ctx.num_exprs() > DYNAMIC_MODE_SWITCH_THRESHOLD;

        let mut engine = Self {
            backend: RefCell::new(JITBackend::with_compiler_flags(CRANELIFT_FLAGS.as_deref())),
            input_state_buffer,
            output_state_buffer,
            output_ledge: RefCell::new(output_ledge),
            output_exprs,
            ctx,
            sys,
            upstream_dependents: FxHashMap::default(),
            dirty_registry,
            step_count: 0,
            dynamic_update_mode_switching_enabled,
            snapshots: Vec::default(),
            output_up_to_date: Cell::new(false),
        };
        if dynamic_update_mode_switching_enabled {
            engine.find_leaf_states_upstream_dep();
        }
        engine
    }

    fn find_leaf_states_upstream_dep(&mut self) {
        let mut todo = vec![];
        let mut visited: FxHashMap<ExprRef, FxHashSet<&State>> = FxHashMap::default();
        let num_mutable_states = self.sys.states.len();
        for state in &self.sys.states {
            if let Some(next) = state.next {
                self.ctx[next].for_each_child(|&child| todo.push((next, child)));
                visited.insert(next, FxHashSet::from_iter([state]));
            }
        }
        while let Some((parent, next)) = todo.pop() {
            if visited
                .get(&next)
                .is_some_and(|propagated_roots| visited[&parent].is_subset(propagated_roots))
            {
                continue;
            }
            let parent_roots = visited[&parent].clone();
            visited.entry(next).or_default().extend(parent_roots);
            self.ctx[next].for_each_child(|&child| todo.push((next, child)));
        }
        for (e, dependent_roots) in visited {
            let expr = &self.ctx[e];
            if expr.num_children() == 0 && expr.is_symbol() {
                let dependents = self
                    .upstream_dependents
                    .entry(e)
                    .or_insert_with(|| FixedBitSet::with_capacity(num_mutable_states));
                for root in dependent_roots {
                    let offset = self.input_state_buffer.get_state_offset(root.symbol);
                    if offset < num_mutable_states {
                        dependents.insert(offset);
                    }
                }
            }
        }
    }

    fn eval_expr(&self, expr: ExprRef) -> SlotData {
        self.backend
            .borrow_mut()
            .eval_expr(expr, self.ctx, &self.input_state_buffer)
    }

    fn step_transition_sys(&mut self) {
        self.backend.borrow_mut().step_transition_sys(
            self.ctx,
            self.sys,
            &self.input_state_buffer,
            &mut self.output_state_buffer,
        );
        self.cached_states_shootdown();
    }

    fn step_dirty_states(&mut self) {
        for offset in self.dirty_registry.states.ones() {
            let next = self.sys.states[offset].next.unwrap();
            let entry = self
                .output_state_buffer
                .ledge
                .entry(self.sys.states[offset].symbol)
                .unwrap();
            self.backend.borrow_mut().eval_expr_with_output_slot(
                next,
                self.ctx,
                &self.input_state_buffer,
                entry,
            );
        }
        self.output_up_to_date.set(false);
    }

    fn try_fetch_from_latest_outputs(&self, expr: ExprRef) -> Option<baa::Value> {
        if !self.output_up_to_date.get() {
            self.backend.borrow_mut().batched_eval_output_exprs(
                self.ctx,
                &self.output_exprs,
                &self.input_state_buffer,
                &mut self.output_ledge.borrow_mut(),
            );
            self.output_up_to_date.set(true);
        }
        self.output_ledge
            .borrow()
            .get_slot_data(expr)
            .map(|data| data.reduce(BaaValueConverter))
    }

    fn swap_state_buffer(&mut self) {
        // SAFETY: input and output state buffer are guaranteed to contain the same slot layout
        unsafe {
            self.input_state_buffer.swap(&mut self.output_state_buffer);
        }
        if self.dynamic_update_mode_switching_enabled {
            self.mark_dirty_states();
            std::mem::swap(
                &mut self.dirty_registry.states,
                &mut self.dirty_registry.scratch_states,
            );
        }
    }

    fn cached_states_shootdown(&mut self) {
        if self.dynamic_update_mode_switching_enabled {
            self.dirty_registry.states.insert_range(..);
        }
        self.output_up_to_date.set(false);
    }

    /// Inspect current state and next state to find those that are modified in last `step` call;
    /// Schedule them to be re-computed at next `step` by adding them to `dirty_states`
    fn mark_dirty_states(&mut self) {
        let states_require_reexamine = &self.dirty_registry.states;
        let next_step_dirty_states = &mut self.dirty_registry.scratch_states;
        next_step_dirty_states.clear();
        // Correctness relies on the fact that mutable state is always put at the front of the slot
        for offset in states_require_reexamine.ones() {
            let current = self
                .input_state_buffer
                .ledge
                .get_slot_data_at_offset(offset);
            let next = self
                .output_state_buffer
                .ledge
                .get_slot_data_at_offset(offset);
            if check_slot_dirtiness(current, next)
                && let Some(roots) = self
                    .upstream_dependents
                    .get(&self.sys.states[offset].symbol)
            {
                next_step_dirty_states.union_with(roots);
            }
        }
    }
}

fn check_slot_dirtiness(a: SlotDataRef<'_>, b: SlotDataRef<'_>) -> bool {
    if matches!(a.tpe, expr::Type::BV(_)) {
        a.ne(&b)
    } else {
        // TODO: Currently for input array, compiler might steal the previous input array.
        // We always conservatively assume that array symbol is always dirty
        true
    }
}

impl patronus::sim::Simulator for JITEngine<'_> {
    type SnapshotId = u32;
    fn init(&mut self, kind: patronus::sim::InitKind) {
        let mut generator = patronus::sim::InitValueGenerator::from_kind(kind);
        for mut data in &mut self.input_state_buffer.ledge {
            let init_value = generator.generate(data.tpe);
            data.reduce(BaaValueSetter(&init_value));
        }

        for state in &self.sys.states {
            if let Some(init) = state.init {
                let ret = self.eval_expr(init);
                self.input_state_buffer
                    .ledge
                    .entry(state.symbol)
                    .unwrap()
                    .insert(ret);
            }
        }
        self.cached_states_shootdown();
    }

    fn step(&mut self) {
        if !self.dynamic_update_mode_switching_enabled
            || matches!(
                self.dirty_registry.select_update_policy(),
                DirtyUpdatePolicy::Batched
            )
        {
            self.step_transition_sys();
        } else {
            self.step_dirty_states();
        }
        self.swap_state_buffer();
        self.step_count += 1;
    }

    fn set<'a>(&mut self, expr: ExprRef, value: impl Into<BitVecValueRef<'a>>) {
        // reset both the input and output state buffer to make sure if `expr` is part of input,
        // its change is reflected in both buffers.

        let vref = value.into();
        for state_buffer in [&mut self.input_state_buffer, &mut self.output_state_buffer] {
            state_buffer
                .ledge
                .get_slot_data_mut(expr)
                .unwrap()
                .expect_bit_vec()
                .copy_from_slice(vref.words());
        }
        if let Some(roots) = self.upstream_dependents.get(&expr) {
            self.dirty_registry.register(roots)
        }
        self.output_up_to_date.set(false);
    }

    fn get(&self, expr: ExprRef) -> baa::Value {
        if let Some(data) = self.try_fetch_from_latest_outputs(expr) {
            data
        } else if let Some(slot) = self.input_state_buffer.ledge.get_slot_data(expr) {
            slot.reduce(BaaValueConverter)
        } else {
            self.eval_expr(expr).as_ref().reduce(BaaValueConverter)
        }
    }

    fn step_count(&self) -> u64 {
        self.step_count
    }

    fn take_snapshot(&mut self) -> Self::SnapshotId {
        let id = self.snapshots.len() as u32;
        self.snapshots.push(self.input_state_buffer.clone());
        id
    }

    fn restore_snapshot(&mut self, id: Self::SnapshotId) {
        self.input_state_buffer = self.snapshots[id as usize].clone();
    }
}
