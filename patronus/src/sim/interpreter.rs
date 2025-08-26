// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use super::{InitKind, InitValueGenerator, Simulator};
use crate::expr::*;
use crate::sim::wave::Wavedump;
use crate::system::*;
use baa::*;
use std::path::Path;

/// Interpreter based simulator for a transition system.
pub struct Interpreter {
    ctx: Context,
    sys: TransitionSystem,
    step_count: u64,
    data: SymbolValueStore,
    snapshots: Vec<SymbolValueStore>,
    wavedump: Option<Wavedump>,
    #[allow(dead_code)]
    do_trace: bool,
}

impl Interpreter {
    pub fn new(ctx: &Context, sys: &TransitionSystem) -> Self {
        Self::internal_new(ctx, sys, false, None)
    }

    pub fn new_with_trace(ctx: &Context, sys: &TransitionSystem) -> Self {
        Self::internal_new(ctx, sys, true, None)
    }

    pub fn new_with_wavedump(
        ctx: &Context,
        sys: &TransitionSystem,
        filename: impl AsRef<Path>,
    ) -> Self {
        let wavedump = Wavedump::open_fst(filename, ctx, sys)
            .expect("Failed to open FST for waveform dumping");
        Self::internal_new(ctx, sys, true, Some(wavedump))
    }

    fn internal_new(
        ctx: &Context,
        sys: &TransitionSystem,
        do_trace: bool,
        wavedump: Option<Wavedump>,
    ) -> Self {
        // TODO: we do not need a copy of the full context, only of the part that is relevant to
        //       the transition system. Once we implement garbage collection, we should use that!

        Self {
            ctx: ctx.clone(),
            sys: sys.clone(),
            step_count: 0,
            data: Default::default(),
            snapshots: vec![],
            do_trace,
            wavedump,
        }
    }

    fn dump_signals(&mut self) {
        if self.wavedump.is_some() {
            let signals = self.wavedump.as_ref().unwrap().signals();
            let values: Vec<_> = signals
                .into_iter()
                .map(|e| {
                    if let Value::BitVec(v) = self.get(e) {
                        Some(v)
                    } else {
                        None
                    }
                })
                .collect();
            self.wavedump
                .as_mut()
                .unwrap()
                .dump_signals(values, self.step_count)
                .expect("failed to write signal values");
        }
    }
}

fn init_signal(
    ctx: &Context,
    state: &mut SymbolValueStore,
    symbol: ExprRef,
    generator: &mut InitValueGenerator,
) {
    let tpe = ctx[symbol].get_type(ctx);
    match generator.generate(tpe) {
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
        let mut generator = InitValueGenerator::from_kind(kind);

        self.data.clear();

        // allocate space for inputs, and states
        for state in self.sys.states.iter() {
            init_signal(&self.ctx, &mut self.data, state.symbol, &mut generator);
        }
        for &symbol in self.sys.inputs.iter() {
            init_signal(&self.ctx, &mut self.data, symbol, &mut generator);
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
        // dump all signal values right before the step.
        self.dump_signals();

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

        // increment step count
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
