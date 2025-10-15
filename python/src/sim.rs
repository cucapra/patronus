use crate::TransitionSystem;
use crate::ctx::ContextGuardRead;
use patronus::expr::ExprRef;
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

    // fn __getitem__(&self, key: ExprRef) -> Option<BigInt> {
    //
    // }
}

#[pyfunction]
#[pyo3(name = "Interpreter")]
pub fn interpreter(sys: &TransitionSystem) -> Simulator {
    let interp = ::patronus::sim::Interpreter::new(ContextGuardRead::default().deref(), &sys.0);
    Simulator(interp)
}
