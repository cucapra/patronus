use ::patronus::btor2;
use ::patronus::expr::SerializableIrNode;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use std::ops::{Deref, DerefMut};
use std::sync::{LazyLock, RwLock, RwLockWriteGuard};

/// Context that is used by default for all operations.
/// Python usage is expected to be less performance critical, so using a single global
/// context seems acceptable and will simplify use.
static DEFAULT_CONTEXT: LazyLock<RwLock<::patronus::expr::Context>> =
    LazyLock::new(|| RwLock::new(::patronus::expr::Context::default()));

#[pyclass]
pub struct TransitionSystem(::patronus::system::TransitionSystem);

/// Exposes the Context object to python
#[pyclass]
pub struct Context(::patronus::expr::Context);

#[pymethods]
impl TransitionSystem {
    #[getter]
    fn name(&self) -> &str {
        &self.0.name
    }

    fn __str__(&self) -> String {
        self.0
            .serialize_to_str(DEFAULT_CONTEXT.read().unwrap().deref())
    }
}

enum ContextGuardMut<'a> {
    Local(&'a mut Context),
    Shared(RwLockWriteGuard<'a, ::patronus::expr::Context>),
}

impl<'a> From<Option<&'a mut Context>> for ContextGuardMut<'a> {
    fn from(value: Option<&'a mut Context>) -> Self {
        value
            .map(|ctx| Self::Local(ctx))
            .unwrap_or_else(|| Self::Shared(DEFAULT_CONTEXT.write().unwrap()))
    }
}

impl<'a> ContextGuardMut<'a> {
    fn deref_mut(&mut self) -> &mut ::patronus::expr::Context {
        match self {
            ContextGuardMut::Local(ctx) => &mut ctx.0,
            ContextGuardMut::Shared(guard) => guard.deref_mut(),
        }
    }
}

#[pyfunction]
#[pyo3(signature = (content, name=None, ctx=None))]
pub fn parse_btor2_str(
    content: &str,
    name: Option<&str>,
    ctx: Option<&mut Context>,
) -> PyResult<TransitionSystem> {
    let mut ctx_guard: ContextGuardMut = ctx.into();
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
