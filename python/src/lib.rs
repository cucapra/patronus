mod ctx;
mod expr;
mod sim;

pub use ctx::Context;
use ctx::{ContextGuardRead, ContextGuardWrite};
pub use expr::*;
pub use sim::{Simulator, interpreter};
use std::path::PathBuf;

use ::patronus::btor2;
use ::patronus::expr::SerializableIrNode;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;

#[pyclass]
#[derive(Clone)]
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
#[derive(Clone)]
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
    #[new]
    #[pyo3(signature = (name, inputs=None, states=None, outputs=None, bad_states=None, constraints=None))]
    fn create(
        name: &str,
        inputs: Option<Vec<ExprRef>>,
        states: Option<Vec<State>>,
        outputs: Option<Vec<Output>>,
        bad_states: Option<Vec<ExprRef>>,
        constraints: Option<Vec<ExprRef>>,
    ) -> Self {
        Self(::patronus::system::TransitionSystem {
            name: name.to_string(),
            states: states
                .map(|v| v.into_iter().map(|e| e.0).collect())
                .unwrap_or_default(),
            inputs: inputs
                .map(|v| v.into_iter().map(|e| e.0).collect())
                .unwrap_or_default(),
            outputs: outputs
                .map(|v| v.into_iter().map(|e| e.0).collect())
                .unwrap_or_default(),
            bad_states: bad_states
                .map(|v| v.into_iter().map(|e| e.0).collect())
                .unwrap_or_default(),
            constraints: constraints
                .map(|v| v.into_iter().map(|e| e.0).collect())
                .unwrap_or_default(),
            names: Default::default(),
        })
    }

    #[getter]
    fn name(&self) -> &str {
        &self.0.name
    }

    #[setter(name)]
    fn set_name(&mut self, name: &str) {
        self.0.name = name.to_string();
    }

    #[getter]
    fn inputs(&self) -> Vec<ExprRef> {
        self.0.inputs.iter().map(|e| ExprRef(*e)).collect()
    }

    #[setter(inputs)]
    fn set_inputs(&mut self, inputs: Vec<ExprRef>) {
        // TODO: validate that all inputs are symbols!
        self.0.inputs = inputs.into_iter().map(|e| e.0).collect();
    }

    #[getter]
    fn outputs(&self) -> Vec<Output> {
        self.0.outputs.iter().map(|e| Output(*e)).collect()
    }

    #[setter(outputs)]
    fn set_outputs(&mut self, outputs: Vec<Output>) {
        self.0.outputs = outputs.into_iter().map(|e| e.0).collect();
    }

    #[getter]
    fn states(&self) -> Vec<State> {
        self.0.states.iter().map(|e| State(*e)).collect()
    }

    #[setter(states)]
    fn set_states(&mut self, states: Vec<State>) {
        self.0.states = states.into_iter().map(|e| e.0).collect();
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

    /// look up states
    fn __getitem__(&self, key: &str) -> Option<State> {
        let ctx_guard = ContextGuardRead::default();
        let ctx = ctx_guard.deref();
        self.0
            .states
            .iter()
            .find(|s| ctx.get_symbol_name(s.symbol).unwrap() == key)
            .map(|s| State(*s))
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
    // sim
    m.add_function(wrap_pyfunction!(interpreter, m)?)?;
    // expr
    m.add_function(wrap_pyfunction!(bit_vec, m)?)?;
    m.add_function(wrap_pyfunction!(bit_vec_val, m)?)?;
    m.add_function(wrap_pyfunction!(if_expr, m)?)?;
    Ok(())
}
