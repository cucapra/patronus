// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ctx::ContextGuardRead;
use crate::{ExprRef, TransitionSystem};
use baa::{BitVecOps, Value};
use num_bigint::BigInt;
use patronus::sim::InitKind;
use pyo3::prelude::*;

#[pyclass]
pub struct Simulator(::patronus::sim::Interpreter);

#[pymethods]
impl Simulator {
    pub fn init(&mut self) {
        use patronus::sim::Simulator;
        self.0.init(InitKind::Zero);
    }

    pub fn step(&mut self) {
        use patronus::sim::Simulator;
        self.0.step();
    }

    /// access the value of an expression
    fn __getitem__(&self, key: ExprRef) -> Option<BigInt> {
        use patronus::sim::Simulator;
        let value = self.0.get(key.0);
        match value {
            Value::Array(_) => {
                todo!("Array support!")
            }
            Value::BitVec(bv) => Some(bv.to_big_int()),
        }
    }
}

#[pyfunction]
#[pyo3(name = "Interpreter")]
pub fn interpreter(sys: &TransitionSystem) -> Simulator {
    let interp = ::patronus::sim::Interpreter::new(ContextGuardRead::default().deref(), &sys.0);
    Simulator(interp)
}
