mod ctx;
mod sim;

use std::path::{PathBuf};
pub use ctx::Context;
use ctx::{ContextGuardRead, ContextGuardWrite};

use ::patronus::btor2;
use ::patronus::expr::SerializableIrNode;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;

#[pyclass]
pub struct ExprRef(::patronus::expr::ExprRef);

#[pymethods]
impl ExprRef {
    fn __str__(&self) -> String {
        self.0.serialize_to_str(ContextGuardRead::default().deref())
    }
}

#[pyclass]
pub struct Output(::patronus::system::Output);

#[pymethods]
impl Output {
    #[getter]
    fn name(&self) -> String {
        ContextGuardRead::default().deref()[self.0.name].to_string()
    }

    #[getter]
    fn expr(&self) -> ExprRef {
        ExprRef(self.0.expr)
    }
}

#[pyclass]
pub struct State(::patronus::system::State);

#[pymethods]
impl State {
    #[getter]
    fn symbol(&self) -> ExprRef {
        ExprRef(self.0.symbol)
    }

    #[getter]
    fn name(&self) -> String {
        ContextGuardRead::default()
            .deref()
            .get_symbol_name(self.0.symbol)
            .unwrap()
            .to_string()
    }

    #[getter]
    fn next(&self) -> Option<ExprRef> {
        self.0.next.map(|e| ExprRef(e))
    }

    #[getter]
    fn init(&self) -> Option<ExprRef> {
        self.0.init.map(|e| ExprRef(e))
    }
}

#[pyclass]
pub struct TransitionSystem(::patronus::system::TransitionSystem);

#[pymethods]
impl TransitionSystem {
    #[getter]
    fn name(&self) -> &str {
        &self.0.name
    }

    #[getter]
    fn inputs(&self) -> Vec<ExprRef> {
        self.0.inputs.iter().map(|e| ExprRef(*e)).collect()
    }

    #[getter]
    fn outputs(&self) -> Vec<Output> {
        self.0.outputs.iter().map(|e| Output(*e)).collect()
    }

    #[getter]
    fn states(&self) -> Vec<State> {
        self.0.states.iter().map(|e| State(*e)).collect()
    }

    #[getter]
    fn bad_states(&self) -> Vec<ExprRef> {
        self.0.bad_states.iter().map(|e| ExprRef(*e)).collect()
    }

    #[getter]
    fn constraints(&self) -> Vec<ExprRef> {
        self.0.constraints.iter().map(|e| ExprRef(*e)).collect()
    }

    fn __str__(&self) -> String {
        self.0.serialize_to_str(ContextGuardRead::default().deref())
    }
}

#[pyfunction]
#[pyo3(signature = (content, name=None))]
pub fn parse_btor2_str(content: &str, name: Option<&str>) -> PyResult<TransitionSystem> {
    let mut ctx_guard = ContextGuardWrite::default();
    let ctx = ctx_guard.deref_mut();
    match btor2::parse_str(ctx, &content, name) {
        Some(sys) => Ok(TransitionSystem(sys)),
        None => Err(PyValueError::new_err("failed to parse btor")),
    }
}

#[pyfunction]
pub fn parse_btor2_file(filename: PathBuf) -> PyResult<TransitionSystem> {
    let mut ctx_guard = ContextGuardWrite::default();
    let ctx = ctx_guard.deref_mut();
    match btor2::parse_file_with_ctx(filename, ctx) {
        Some(sys) => Ok(TransitionSystem(sys)),
        None => Err(PyValueError::new_err("failed to parse btor")),
    }
}

#[pymodule]
#[pyo3(name = "patronus")]
fn patronus(_py: Python<'_>, m: &pyo3::Bound<'_, pyo3::types::PyModule>) -> PyResult<()> {
    m.add_class::<TransitionSystem>()?;
    m.add_class::<ExprRef>()?;
    m.add_class::<Output>()?;
    m.add_class::<State>()?;
    m.add_function(wrap_pyfunction!(parse_btor2_str, m)?)?;
    m.add_function(wrap_pyfunction!(parse_btor2_file, m)?)?;
    Ok(())
}
