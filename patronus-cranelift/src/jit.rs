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
use rustc_hash::FxHashSet;
use slot_new::*;
use std::cell::{Cell, RefCell};
use std::ops::Index;
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

// the set of core 'things' necessary to simulate the btor design,
// packaged into one structure to make interior mutability more convenient.
struct SimAssets {
    transition_fun: EvalFun,
    output_fun: EvalFun,
    state_buf: StateBuf,
}

impl SimAssets {
    fn init_and_comp(flags: Option<&str>, ctx: &expr::Context, sys: &TransitionSystem) -> Self {
        let mut state_buf = StateBuf::default();

        let base_exprs: Vec<_> = sys
            .states
            .iter()
            .map(|s| s.symbol)
            .chain(sys.inputs.clone())
            .collect();
        state_buf.add_exprs(ctx, &base_exprs);

        // create output ledger with associated offsets
        let output_exprs: Vec<_> = Vec::from_iter(
            sys.outputs
                .iter()
                .map(|out| out.expr)
                .chain(sys.bad_states.iter().chain(&sys.constraints).copied())
                .collect::<FxHashSet<_>>(),
        );
        state_buf.add_exprs(ctx, &output_exprs);

        /*
            a note on memory management:

            JITCompiler contains a Box for the heap memory where compiled functions / data go. this should not be deallocated at runtime!

            so far, the compiler is able to keep that memory alive until this struct goes out of scope. the documentation for cranelift JITModule's get_finalized_function reflects that: the pointer remains valid until JITModule::free_memory is called.

            in case it mysteriously fails in the future, that's why
        */
        use compiler::module_helpers::*;

        let mut jit_m = new_m(flags);
        let output_fun = compile_expr_batch(&mut jit_m, ctx, &output_exprs, &mut state_buf)
            .unwrap_or_else(|err| {
                panic!("fail to compiled batched output exprs update, due to {err:?}")
            });
        let transition_fun = compile_transition_sys(&mut jit_m, ctx, sys, &state_buf, &state_buf)
            .unwrap_or_else(|err| {
                panic!("fail to compiled batched output exprs update, due to {err:?}")
            });
        Self {
            output_fun,
            transition_fun,
            state_buf,
        }
    }

    fn batched_eval_output_exprs(&mut self) {
        unsafe { self.output_fun.call(self.state_buf.as_mut_slice()) }
    }

    fn step_transition_sys(&mut self) {
        // SAFETY: jit compiler has not been dropped
        unsafe { self.transition_fun.call(self.state_buf.as_mut_slice()) }
    }
}

pub struct JITEngine<'expr> {
    ctx: &'expr expr::Context,
    sys: &'expr TransitionSystem,
    /// Interior mutability for lazy compilation triggered by `Simulator::get`
    backend: RefCell<SimAssets>,
    step_count: u64,
    snapshots: Vec<StateBuf>,
    output_up_to_date: Cell<bool>,
}

impl<'expr> JITEngine<'expr> {
    pub fn new(ctx: &'expr expr::Context, sys: &'expr TransitionSystem) -> JITEngine<'expr> {
        let back = SimAssets::init_and_comp(CRANELIFT_FLAGS.as_deref(), ctx, sys);
        Self {
            backend: RefCell::new(back),
            ctx,
            sys,
            step_count: 0,
            snapshots: Vec::default(),
            output_up_to_date: Cell::new(false),
        }
    }

    fn step_transition_sys(&mut self) {
        self.backend.borrow_mut().step_transition_sys();
        self.output_up_to_date.set(false);
    }

    fn try_fetch_from_latest_outputs(&self, expr: ExprRef) -> Option<baa::Value> {
        {
            let b = &self.backend.borrow().state_buf;
            if !b.contains(expr) {
                return None;
            }
        }

        if !self.output_up_to_date.get() {
            self.backend.borrow_mut().batched_eval_output_exprs();
            self.output_up_to_date.set(true);
        }
        let b = &self.backend.borrow().state_buf;
        Some(baa::Value::BitVec(b.get_slot(expr)))
    }
}

impl patronus::sim::Simulator for JITEngine<'_> {
    type SnapshotId = u32;
    fn init(&mut self, kind: patronus::sim::InitKind) {
        let mut generator = patronus::sim::InitValueGenerator::from_kind(kind);
        let state_r = &mut self.backend.borrow_mut().state_buf;
        state_r.init(&mut generator);

        for state in &self.sys.states {
            if let Some(init) = state.init {
                let backing_ex = self.ctx.index(init);
                let offset = state_r.offset_query(state.symbol).unwrap();

                match backing_ex {
                    Expr::BVLiteral(b) => {
                        let r = b.get(self.ctx);
                        state_r.set_slot(offset, r.words());
                    }
                    _ => {
                        let res = eval_expr(self.ctx, state_r, init);
                        if let Value::BitVec(i) = res {
                            state_r.set_slot(offset, i.words())
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
        let state_r = &mut self.backend.borrow_mut().state_buf;

        let offset = state_r.offset_query(expr).unwrap();
        state_r.set_slot(offset, vref.words());
        self.output_up_to_date.set(false);
    }

    fn set_array(&mut self, _expr: ExprRef, _value: ArrayValue) {
        panic!("using array values in cranelift backend")
    }

    fn get(&self, expr: ExprRef) -> baa::Value {
        if let Some(data) = self.try_fetch_from_latest_outputs(expr) {
            data
        } else {
            let state_r = &self.backend.borrow().state_buf;
            if state_r.contains(expr) {
                baa::Value::BitVec(state_r.get_slot(expr))
            } else {
                eval_expr(self.ctx, state_r, expr)
            }
        }
    }

    fn step_count(&self) -> u64 {
        self.step_count
    }

    fn take_snapshot(&mut self) -> Self::SnapshotId {
        let id = self.snapshots.len() as u32;
        let saved = self.backend.borrow().state_buf.clone();
        self.snapshots.push(saved);
        id
    }

    fn restore_snapshot(&mut self, id: Self::SnapshotId) {
        let state_r = &mut self.backend.borrow_mut().state_buf;
        *state_r = self.snapshots[id as usize].clone();
    }
}
