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
<<<<<<< HEAD
use rustc_hash::FxHashSet;
use slot_new::*;
use std::cell::{Cell, Ref, RefCell};
use std::ops::Index;
=======
use rustc_hash::{FxHashMap, FxHashSet};
use slot_new::*;
use std::cell::{Cell, RefCell};
>>>>>>> a3b17debde7669d0fa51defd26cba7ffaccc9ca7
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
<<<<<<< HEAD
    compiled_transition_sys: Option<EvalFun>,
    out_exprs_fun: Option<EvalFun>,
=======
    compiled_transition_sys: Option<EvalBatchedExprWithUpdate>,
    compiled_expr_eval: FxHashMap<ExprRef, EvalBatchedExprWithUpdate>,
    compiled_output_exprs_batched_update: Option<EvalBatchedExprWithUpdate>,
>>>>>>> a3b17debde7669d0fa51defd26cba7ffaccc9ca7
}

impl JITBackend {
    fn with_compiler_flags(flags: Option<&str>) -> Self {
        Self {
            compiler: JITCompiler::new(flags),
            compiled_transition_sys: None,
<<<<<<< HEAD
            out_exprs_fun: None,
        }
    }

=======
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

>>>>>>> a3b17debde7669d0fa51defd26cba7ffaccc9ca7
    fn batched_eval_output_exprs(
        &mut self,
        ctx: &expr::Context,
        output_exprs: &[ExprRef],
<<<<<<< HEAD
        state_buf: &mut StateBuf,
    ) {
        let eval_fn = self.out_exprs_fun.get_or_insert_with(|| {
            // print!("batch compile:");
            // for e in output_exprs {
            //     print!("{}", e.serialize_to_str(ctx));
            // }
            // println!();

            self.compiler
                .compile_batched_expr_eval(ctx, output_exprs, state_buf)
                .unwrap_or_else(|err| {
                    panic!("fail to compiled batched output exprs update, due to {err:?}")
                })
        });
=======
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
>>>>>>> a3b17debde7669d0fa51defd26cba7ffaccc9ca7
        // print!("batch:");
        // for e in output_exprs {
        //     print!("{}", e.serialize_to_str(ctx));
        // }
        // println!();
<<<<<<< HEAD
        unsafe { eval_fn.call(state_buf.as_mut_slice()) }
=======
        unsafe {
            eval_fn.call(
                input_state_buffer.as_slice(),
                output_state_buffer.as_mut_slice(),
            )
        }
>>>>>>> a3b17debde7669d0fa51defd26cba7ffaccc9ca7
    }

    fn step_transition_sys(
        &mut self,
        ctx: &expr::Context,
        sys: &TransitionSystem,
<<<<<<< HEAD
        state_buf: &mut StateBuf,
=======
        input_state_buffer: &StateBuf,
        output_state_buffer: &mut StateBuf,
>>>>>>> a3b17debde7669d0fa51defd26cba7ffaccc9ca7
    ) {
        // attempt compilation if transition sys has not been compiled yet, or otherwise use the existing result
        let eval_fn = self.compiled_transition_sys.get_or_insert_with(|| {
            // println!("compiling transition sys");
            self.compiler
<<<<<<< HEAD
                .compile_transition_sys(ctx, sys, state_buf, state_buf)
=======
                .compile_transition_sys(ctx, sys, input_state_buffer, &*output_state_buffer)
>>>>>>> a3b17debde7669d0fa51defd26cba7ffaccc9ca7
                .unwrap_or_else(|err| {
                    panic!("fail to compile transition step function, due to {err:?}")
                })
        });
        // println!("evaluating transition sys");

        // SAFETY: jit compiler has not been dropped
<<<<<<< HEAD
        unsafe { eval_fn.call(state_buf.as_mut_slice()) }
=======
        unsafe {
            eval_fn.call(
                input_state_buffer.as_slice(),
                output_state_buffer.as_mut_slice(),
            )
        }
>>>>>>> a3b17debde7669d0fa51defd26cba7ffaccc9ca7
    }
}

pub struct JITEngine<'expr> {
<<<<<<< HEAD
    in_state: RefCell<StateBuf>,
=======
    in_state: StateBuf,
    out_state: StateBuf,
    // state: JITState,
    /// Value placeholders for output expressions, including `output`, `bad` and `constraint`
    output_ledge: RefCell<StateBuf>,
>>>>>>> a3b17debde7669d0fa51defd26cba7ffaccc9ca7
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
        let mut in_state = StateBuf::default();

        let base_exprs: Vec<_> = sys
            .states
            .iter()
            .map(|s| s.symbol)
            .chain(sys.inputs.clone())
            .collect();
        in_state.add_exprs(ctx, &base_exprs);

        // create output ledger with associated offsets
        let output_exprs: Vec<_> = Vec::from_iter(
            sys.outputs
                .iter()
                .map(|out| out.expr)
                .chain(sys.bad_states.iter().chain(&sys.constraints).copied())
                .collect::<FxHashSet<_>>(),
        );
        in_state.add_exprs(ctx, &output_exprs);

        let engine = Self {
            backend: RefCell::new(JITBackend::with_compiler_flags(CRANELIFT_FLAGS.as_deref())),
            in_state: RefCell::new(in_state),
            output_exprs,
            ctx,
            sys,
            step_count: 0,
            snapshots: Vec::default(),
            output_up_to_date: Cell::new(false),
        };

        engine
    }

    fn step_transition_sys(&mut self) {
        self.backend.borrow_mut().step_transition_sys(
            self.ctx,
            self.sys,
        );
        self.output_up_to_date.set(false);
    }

    fn try_fetch_from_latest_outputs(&self, expr: ExprRef) -> Option<baa::Value> {
        if !self.in_state.borrow().contains(expr) {
            return None;
        }
        if !self.output_up_to_date.get() {
            self.backend.borrow_mut().batched_eval_output_exprs(
                self.ctx,
                &self.output_exprs,
                &mut self.in_state.borrow_mut(),
            );
            self.output_up_to_date.set(true);
        }
        Some(baa::Value::BitVec(self.in_state.borrow().get_slot(expr)))
    }
}

impl patronus::sim::Simulator for JITEngine<'_> {
    type SnapshotId = u32;
    fn init(&mut self, kind: patronus::sim::InitKind) {
        let mut generator = patronus::sim::InitValueGenerator::from_kind(kind);
        self.in_state.borrow_mut().init(&mut generator);

        for state in &self.sys.states {
            if let Some(init) = state.init {
                let backing_ex = self.ctx.index(init);
                let offset = self.in_state.borrow().offset_query(state.symbol).unwrap();

                match backing_ex {
                    Expr::BVLiteral(b) => {
                        let r = b.get(self.ctx);
                        self.in_state.borrow_mut().set_slot(offset, r.words());
                    }
                    _ => {
                        let state_ref = self.in_state.get_mut();
                        let res = eval_expr(self.ctx, state_ref, init);
                        if let Value::BitVec(i) = res {
                            self.in_state.borrow_mut().set_slot(offset, i.words())
                        } else {
                            panic!("got array out of evaluation")
                        }
                    }
                };
            }
        }
        self.output_up_to_date.set(false);
    }

    fn step(&mut self) {
        self.step_transition_sys();
        self.step_count += 1;
    }

    fn set<'a>(&mut self, expr: ExprRef, value: impl Into<BitVecValueRef<'a>>) {
        // reset both the input and output state buffer to make sure if `expr` is part of input,
        // its change is reflected in both buffers.

        let vref = value.into();
        let offset = self.in_state.borrow().offset_query(expr).unwrap();
        self.in_state.borrow_mut().set_slot(offset, vref.words());
        self.output_up_to_date.set(false);
    }

    fn set_array(&mut self, _expr: ExprRef, _value: ArrayValue) {
        panic!("using array values in cranelift backend")
    }

    fn get(&self, expr: ExprRef) -> baa::Value {
        if let Some(data) = self.try_fetch_from_latest_outputs(expr) {
            data
        } else if self.in_state.borrow().contains(expr) {
            baa::Value::BitVec(self.in_state.borrow().get_slot(expr))
        } else {
            // NOTE: this is extremely dumb, but is the only way i could find to work around the refcell containing InState
            let state_ref = self.in_state.borrow().clone();
            eval_expr(self.ctx, &state_ref, expr)
        }
    }

    fn step_count(&self) -> u64 {
        self.step_count
    }

    fn take_snapshot(&mut self) -> Self::SnapshotId {
        let id = self.snapshots.len() as u32;
        self.snapshots.push(self.in_state.borrow().clone());
        id
    }

    fn restore_snapshot(&mut self, id: Self::SnapshotId) {
        self.in_state.replace(self.snapshots[id as usize].clone());
    }
}
