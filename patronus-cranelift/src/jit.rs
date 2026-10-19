// Copyright 2025-2026 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
// author: Willow Ge <lg634@cornell.edu>
mod bv_codegen;
mod compiler;
mod expr_graph;
mod slot_new;

use baa::*;
use compiler::*;
use cranelift::module::ModuleError;
use patronus::expr::{self, *};
use patronus::system::*;
use rustc_hash::{FxHashMap, FxHashSet};
use slot_new::*;
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
/// Extra cranelift settings that will be directly passed to JIT compiler.
/// This should be a colon separated key value pair joined by comma.
static CRANELIFT_FLAGS: LazyLock<Option<String>> =
    LazyLock::new(|| std::env::var("CRANELIFT_FLAGS").ok());
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
        input_state_buffer: &StateBuf,
        entry: &mut u64,
    ) {
        let eval_fn = self.compiled_expr_eval.entry(expr).or_insert_with(|| {
            println!("compiling {}", expr.serialize_to_str(ctx));
            self.compiler
                .compile_batched_expr_eval(
                    ctx,
                    &[expr],
                    input_state_buffer,
                    &mut StateBuf::new_singleton(ctx, expr),
                )
                .unwrap_or_else(|err| panic!("fail to compile: `{:?}` due to {:?}", ctx[expr], err))
        });
        // println!("evaluating {}", expr.serialize_to_str(ctx));
        // SAFETY: jit compiler has not been dropped
        unsafe {
            eval_fn.call(input_state_buffer.as_slice(), std::slice::from_mut(entry));
        }
    }

    fn eval_expr(
        &mut self,
        expr: ExprRef,
        ctx: &expr::Context,
        input_state_buffer: &StateBuf,
    ) -> BitVecValue {
        let mut out_dest: u64 = 0;
        self.eval_expr_with_output_slot(expr, ctx, input_state_buffer, &mut out_dest);
        BitVecValue::from_u64(out_dest, expr.get_bv_type(ctx).unwrap())
    }

    fn batched_eval_output_exprs(
        &mut self,
        ctx: &expr::Context,
        output_exprs: &[ExprRef],
        input_state_buffer: &StateBuf,
        output_state_buffer: &mut StateBuf,
    ) {
        let eval_fn = self
            .compiled_output_exprs_batched_update
            .get_or_insert_with(|| {
                // print!("batch compile:");
                // for e in output_exprs {
                //     print!("{}", e.serialize_to_str(ctx));
                // }
                // println!();

                self.compiler
                    .compile_batched_expr_eval(
                        ctx,
                        output_exprs,
                        input_state_buffer,
                        output_state_buffer,
                    )
                    .unwrap_or_else(|err| {
                        panic!("fail to compiled batched output exprs update, due to {err:?}")
                    })
            });
        // print!("batch:");
        // for e in output_exprs {
        //     print!("{}", e.serialize_to_str(ctx));
        // }
        // println!();
        unsafe {
            eval_fn.call(
                input_state_buffer.as_slice(),
                output_state_buffer.as_mut_slice(),
            )
        }
    }

    fn step_transition_sys(
        &mut self,
        ctx: &expr::Context,
        sys: &TransitionSystem,
        input_state_buffer: &StateBuf,
        output_state_buffer: &mut StateBuf,
    ) {
        // attempt compilation if transition sys has not been compiled yet, or otherwise use the existing result
        let eval_fn = self.compiled_transition_sys.get_or_insert_with(|| {
            // println!("compiling transition sys");
            self.compiler
                .compile_transition_sys(ctx, sys, input_state_buffer, &*output_state_buffer)
                .unwrap_or_else(|err| {
                    panic!("fail to compile transition step function, due to {err:?}")
                })
        });
        // println!("evaluating transition sys");

        // SAFETY: jit compiler has not been dropped
        unsafe {
            eval_fn.call(
                input_state_buffer.as_slice(),
                output_state_buffer.as_mut_slice(),
            )
        }
    }
}

pub struct JITEngine<'expr> {
    in_state: StateBuf,
    out_state: StateBuf,
    // state: JITState,
    /// Value placeholders for output expressions, including `output`, `bad` and `constraint`
    output_ledge: RefCell<StateBuf>,
    output_exprs: Vec<ExprRef>,
    ctx: &'expr expr::Context,
    sys: &'expr TransitionSystem,
    /// Interior mutability for lazy compilation triggered by `Simulator::get`
    backend: RefCell<JITBackend>,
    step_count: u64,
    snapshots: Vec<StateBuf>,
    output_up_to_date: Cell<bool>,
}

impl<'expr> JITEngine<'expr> {
    pub fn new(ctx: &'expr expr::Context, sys: &'expr TransitionSystem) -> JITEngine<'expr> {
        let in_state = StateBuf::new(ctx, sys);
        let out_state = in_state.clone();

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
        let output_ledge = StateBuf::new_exprset(ctx, &output_exprs, output_exprs_to_offset);

        let engine = Self {
            backend: RefCell::new(JITBackend::with_compiler_flags(CRANELIFT_FLAGS.as_deref())),
            in_state,
            out_state,
            output_ledge: RefCell::new(output_ledge),
            output_exprs,
            ctx,
            sys,
            step_count: 0,
            snapshots: Vec::default(),
            output_up_to_date: Cell::new(false),
        };

        engine
    }

    fn eval_expr(&self, expr: ExprRef) -> baa::BitVecValue {
        self.backend
            .borrow_mut()
            .eval_expr(expr, self.ctx, &self.in_state)
    }

    fn step_transition_sys(&mut self) {
        self.backend.borrow_mut().step_transition_sys(
            self.ctx,
            self.sys,
            &self.in_state,
            &mut self.out_state,
        );
        self.output_up_to_date.set(false);
    }

    fn try_fetch_from_latest_outputs(&self, expr: ExprRef) -> Option<baa::Value> {
        if !self.output_ledge.borrow().contains(expr) {
            return None;
        }
        if !self.output_up_to_date.get() {
            self.backend.borrow_mut().batched_eval_output_exprs(
                self.ctx,
                &self.output_exprs,
                &self.in_state,
                &mut self.output_ledge.borrow_mut(),
            );
            self.output_up_to_date.set(true);
        }
        Some(baa::Value::BitVec(
            self.output_ledge.borrow().get_slot(expr),
        ))
    }
}

impl patronus::sim::Simulator for JITEngine<'_> {
    type SnapshotId = u32;
    fn init(&mut self, kind: patronus::sim::InitKind) {
        let mut generator = patronus::sim::InitValueGenerator::from_kind(kind);
        self.in_state.init(&mut generator);

        for state in &self.sys.states {
            if let Some(init) = state.init {
                let ret = self.eval_expr(init);
                let offset = self.in_state.offset_query(state.symbol).unwrap();
                self.in_state.set_slot(offset, ret.words());
            }
        }
        self.output_up_to_date.set(false);
    }

    fn step(&mut self) {
        self.step_transition_sys();
        self.in_state.swap(&mut self.out_state);

        self.step_count += 1;
    }

    fn set<'a>(&mut self, expr: ExprRef, value: impl Into<BitVecValueRef<'a>>) {
        // reset both the input and output state buffer to make sure if `expr` is part of input,
        // its change is reflected in both buffers.

        let vref = value.into();
        let offset = self.in_state.offset_query(expr).unwrap();
        self.in_state.set_slot(offset, vref.words());
        self.out_state.set_slot(offset, vref.words());
        self.output_up_to_date.set(false);
    }

    fn set_array(&mut self, _expr: ExprRef, _value: ArrayValue) {
        panic!("using array values in cranelift backend")
    }

    fn get(&self, expr: ExprRef) -> baa::Value {
        if let Some(data) = self.try_fetch_from_latest_outputs(expr) {
            data
        } else if self.in_state.contains(expr) {
            baa::Value::BitVec(self.in_state.get_slot(expr))
        } else {
            baa::Value::BitVec(self.eval_expr(expr))
        }
    }

    fn step_count(&self) -> u64 {
        self.step_count
    }

    fn take_snapshot(&mut self) -> Self::SnapshotId {
        let id = self.snapshots.len() as u32;
        self.snapshots.push(self.in_state.clone());
        id
    }

    fn restore_snapshot(&mut self, id: Self::SnapshotId) {
        self.in_state = self.snapshots[id as usize].clone();
    }
}
