// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use super::{InitKind, InitValueGenerator, Simulator};
use crate::expr::*;
use crate::system::*;
use baa::*;

/// Interpreter based simulator for a transition system.
pub struct Interpreter {
    ctx: Context,
    sys: TransitionSystem,
    step_count: u64,
    data: SymbolValueStore,
    snapshots: Vec<SymbolValueStore>,
    #[allow(dead_code)]
    do_trace: bool,
}

impl Interpreter {
    pub fn new(ctx: &Context, sys: &TransitionSystem) -> Self {
        Self::internal_new(ctx, sys, false)
    }

    pub fn new_with_trace(ctx: &Context, sys: &TransitionSystem) -> Self {
        Self::internal_new(ctx, sys, true)
    }

    fn internal_new(ctx: &Context, sys: &TransitionSystem, do_trace: bool) -> Self {
        // TODO: we do not need a copy of the full context, only of the part that is relevant to
        //       the transition system. Once we implement garbage collection, we should use that!

        Self {
            ctx: ctx.clone(),
            sys: sys.clone(),
            step_count: 0,
            data: Default::default(),
            snapshots: vec![],
            do_trace,
        }
    }
}

fn init_signal(
    ctx: &Context,
    state: &mut SymbolValueStore,
    symbol: ExprRef,
    gen: &mut InitValueGenerator,
) {
    let tpe = ctx[symbol].get_type(ctx);
    match gen.gen(tpe) {
        Value::Array(value) => {
            state.define_array(symbol, value);
        }
        Value::BitVec(value) => {
            state.define_bv(symbol, &value);
        }
    }
}

impl Simulator for Interpreter {
    type SnapshotId = u32;

    fn init(&mut self, kind: InitKind) {
        let mut gen = InitValueGenerator::from_kind(kind);

        self.data.clear();

        // allocate space for inputs, and states
        for state in self.sys.states.iter() {
            init_signal(&self.ctx, &mut self.data, state.symbol, &mut gen);
        }
        for &symbol in self.sys.inputs.iter() {
            init_signal(&self.ctx, &mut self.data, symbol, &mut gen);
        }

        // evaluate init expressions
        for state in self.sys.states.iter() {
            if let Some(init) = state.init {
                let value = eval_expr(&self.ctx, &self.data, init);
                self.data.update(state.symbol, value);
            }
        }
    }

    fn step(&mut self) {
        // calculate all next states
        let next_states = self
            .sys
            .states
            .iter()
            .map(|s| s.next.map(|n| eval_expr(&self.ctx, &self.data, n)))
            .collect::<Vec<_>>();

        // assign next value to store
        for (state, next_value) in self.sys.states.iter().zip(next_states.into_iter()) {
            if let Some(value) = next_value {
                self.data.update(state.symbol, value);
            }
        }

        // increment step cout
        self.step_count += 1;
    }

    fn set<'b>(&mut self, expr: ExprRef, value: impl Into<BitVecValueRef<'b>>) {
        self.data.update_bv(expr, value);
    }

    fn get(&self, expr: ExprRef) -> Value {
        eval_expr(&self.ctx, &self.data, expr)
    }

    fn step_count(&self) -> u64 {
        self.step_count
    }

    fn take_snapshot(&mut self) -> Self::SnapshotId {
        let id = self.snapshots.len() as u32;
        self.snapshots.push(self.data.clone());
        id
    }

    fn restore_snapshot(&mut self, id: Self::SnapshotId) {
        self.data = self.snapshots[id as usize].clone();
    }
}
