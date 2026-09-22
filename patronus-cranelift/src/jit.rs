// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
mod bv_codegen;
mod compiler;
mod expr_graph;
mod heap;
mod indep_gen;
mod runtime;
mod slot;
mod store;

use store::*;

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
        input_state_buffer: &StateBuffer,
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
        input_state_buffer: &StateBuffer,
    ) -> SlotData {
        let mut ledge = ExprLedge::new_singleton(ctx, expr);
        self.eval_expr_with_output_slot(expr, ctx, input_state_buffer, ledge.entry_at_offset(0));
        ledge.into_slot_data().into_iter().next().unwrap()
    }

    fn batched_eval_output_exprs(
        &mut self,
        ctx: &expr::Context,
        output_exprs: &[ExprRef],
        input_state_buffer: &StateBuffer,
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
        input_state_buffer: &StateBuffer,
        output_state_buffer: &mut StateBuffer,
    ) {
        // attempt compilation if transition sys has not been compiled yet, or otherwise use the existing result
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

pub struct JITEngine<'expr> {
    state: JITState,
    /// Value placeholders for output expressions, including `output`, `bad` and `constraint`
    output_ledge: RefCell<ExprLedge>,
    output_exprs: Vec<ExprRef>,
    ctx: &'expr expr::Context,
    sys: &'expr TransitionSystem,
    /// Interior mutability for lazy compilation triggered by `Simulator::get`
    backend: RefCell<JITBackend>,
    /// For each leaf state, tracks all root state expr that transitively depends on it
    upstream_dependents: FxHashMap<ExprRef, FixedBitSet>,
    step_count: u64,
    /// Whether dynamic switching is enabled is determined by the number of expr nodes.
    /// When enabled, JIT will switch between per-expr and batched update mode in each `step()` according to the dirty
    /// percetange of output states.
    dynamic_update_mode_switching_enabled: bool,
    snapshots: Vec<StateBuffer>,
    output_up_to_date: Cell<bool>,
}

impl<'expr> JITEngine<'expr> {
    pub fn new(ctx: &'expr expr::Context, sys: &'expr TransitionSystem) -> JITEngine<'expr> {
        let state = JITState::new(ctx, sys);

        // create output ledger with associated offsets
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
        let output_ledge = ExprLedge::new(ctx, &output_exprs, output_exprs_to_offset);

        let dynamic_update_mode_switching_enabled =
            *DYNAMIC_MODE_SWITCH && ctx.num_exprs() > DYNAMIC_MODE_SWITCH_THRESHOLD;

        let mut engine = Self {
            backend: RefCell::new(JITBackend::with_compiler_flags(CRANELIFT_FLAGS.as_deref())),
            state,
            output_ledge: RefCell::new(output_ledge),
            output_exprs,
            ctx,
            sys,
            upstream_dependents: FxHashMap::default(),
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
                    let offset = self.state.in_state.get_state_offset(root.symbol);
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
            .eval_expr(expr, self.ctx, &self.state.in_state)
    }

    fn step_transition_sys(&mut self) {
        self.backend.borrow_mut().step_transition_sys(
            self.ctx,
            self.sys,
            &self.state.in_state,
            &mut self.state.out_state,
        );
        self.cached_states_shootdown();
    }

    fn step_dirty_states(&mut self) {
        for offset in self.state.dirty_registry.states.ones() {
            let stateinfo = self.sys.states[offset];
            let next = stateinfo.next.unwrap();
            let entry = self.state.out_state.ledge.entry(stateinfo.symbol).unwrap();
            self.backend.borrow_mut().eval_expr_with_output_slot(
                next,
                self.ctx,
                &self.state.in_state,
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
                &self.state.in_state,
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
        self.state.swap_states();
        if self.dynamic_update_mode_switching_enabled {
            self.mark_dirty_states();
            self.state.dirty_registry.swap();
        }
    }

    fn cached_states_shootdown(&mut self) {
        if self.dynamic_update_mode_switching_enabled {
            self.state.dirty_registry.shootdown();
        }
        self.output_up_to_date.set(false);
    }

    /// Inspect current state and next state to find those that are modified in last `step` call;
    /// Schedule them to be re-computed at next `step` by adding them to `dirty_states`
    fn mark_dirty_states(&mut self) {
        self.state
            .mark_dirty_states(&self.upstream_dependents, &self.sys);
    }
}

impl patronus::sim::Simulator for JITEngine<'_> {
    type SnapshotId = u32;
    fn init(&mut self, kind: patronus::sim::InitKind) {
        let mut generator = patronus::sim::InitValueGenerator::from_kind(kind);
        self.state.gen_init(&mut generator);

        for state in &self.sys.states {
            if let Some(init) = state.init {
                let ret = self.eval_expr(init);
                self.state
                    .in_state
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
                self.state.dirty_registry.select_update_policy(),
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
        self.state.set(expr, vref);
        if let Some(roots) = self.upstream_dependents.get(&expr) {
            self.state.dirty_registry.register(roots)
        }
        self.output_up_to_date.set(false);
    }

    fn get(&self, expr: ExprRef) -> baa::Value {
        if let Some(data) = self.try_fetch_from_latest_outputs(expr) {
            data
        } else if let Some(slot) = self.state.in_ledge().get_slot_data(expr) {
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
        self.snapshots.push(self.state.in_state.clone());
        id
    }

    fn restore_snapshot(&mut self, id: Self::SnapshotId) {
        self.state.in_state = self.snapshots[id as usize].clone();
    }
}
