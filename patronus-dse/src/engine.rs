// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use patronus::expr::{Context, ExprRef};
use patronus::sim::InitKind;
use patronus::system::TransitionSystem;
use crate::ValueSummary;

/// Symbolic execution engine.
pub struct SymEngine {
    sys: TransitionSystem,
    step_count: u64,
}

pub type SymEngineValue = ValueSummary<ExprRef>;

impl SymEngine {
    pub fn new(_ctx: &Context, sys: TransitionSystem) -> Self {
        Self { sys, step_count: 0 }
    }

    pub fn init(&mut self, kind: InitKind) {
        todo!()
    }

    pub fn step(&mut self) {
        todo!()
    }

    pub fn set<'b>(&mut self, expr: ExprRef, value: SymEngineValue) {
        todo!()
    }

    pub fn get(&self, expr: ExprRef) -> SymEngineValue {
        todo!()
    }

    pub fn step_count(&self) -> u64 {
        self.step_count
    }


}
