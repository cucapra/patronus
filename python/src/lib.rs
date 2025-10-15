mod ctx;
pub use ctx::Context;
use ctx::{ContextGuardRead, ContextGuardWrite};

use ::patronus::btor2;
use ::patronus::expr::SerializableIrNode;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;

#[pyclass]
pub struct TransitionSystem(::patronus::system::TransitionSystem);

#[pymethods]
impl TransitionSystem {
    #[getter]
    fn name(&self) -> &str {
        &self.0.name
    }

    fn __str__(&self) -> String {
        self.0.serialize_to_str(ContextGuardRead::default().deref())
    }
}

#[pyfunction]
#[pyo3(signature = (content, name=None, ctx=None))]
pub fn parse_btor2_str(
    content: &str,
    name: Option<&str>,
    ctx: Option<&mut Context>,
) -> PyResult<TransitionSystem> {
    let mut ctx_guard: ContextGuardWrite = ctx.into();
    let ctx = ctx_guard.deref_mut();
    match btor2::parse_str(ctx, &content, name) {
        Some(sys) => Ok(TransitionSystem(sys)),
        None => Err(PyValueError::new_err("failed to parse btor")),
    }
}

#[pymodule]
#[pyo3(name = "patronus")]
fn patronus(_py: Python<'_>, m: &pyo3::Bound<'_, pyo3::types::PyModule>) -> PyResult<()> {
    m.add_class::<TransitionSystem>()?;
    m.add_function(wrap_pyfunction!(parse_btor2_str, m)?)?;
    Ok(())
}
