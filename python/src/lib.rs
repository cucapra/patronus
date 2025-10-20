// Copyright 2025 The Regents of the University of California
// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Adwait Godbole <adwait@berkeley.edu>

mod ctx;
mod expr;
mod mc;
mod sim;
mod smt;

pub use ctx::Context;
use ctx::{ContextGuardRead, ContextGuardWrite};
pub use expr::*;
pub use mc::*;
pub use sim::{Simulator, interpreter};
pub use smt::*;
use std::path::PathBuf;

use patronus::btor2;
use patronus::expr::{SerializableIrNode, TypeCheck, WidthInt};
use pyo3::exceptions::{PyRuntimeError, PyValueError};
use pyo3::prelude::*;

#[pyclass]
#[derive(Clone)]
pub struct Output(patronus::system::Output);

#[pymethods]
impl Output {
    #[new]
    fn create(name: &str, expr: ExprRef) -> Self {
        let output = patronus::system::Output {
            name: ContextGuardWrite::default().deref_mut().string(name.into()),
            expr: expr.0,
        };
        Self(output)
    }

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
pub struct State(patronus::system::State);

#[pymethods]
impl State {
    #[new]
    #[pyo3(signature = (name, width=None, init=None, next=None))]
    fn create(
        name: &str,
        width: Option<WidthInt>,
        init: Option<ExprRef>,
        next: Option<ExprRef>,
    ) -> PyResult<Self> {
        let mut ctx_guard = ContextGuardWrite::default();
        let ctx = ctx_guard.deref_mut();
        let init_width = init.as_ref().and_then(|i| ctx[i.0].get_bv_type(ctx));
        let next_width = next.as_ref().and_then(|n| ctx[n.0].get_bv_type(ctx));
        let width = width.or(init_width).or(next_width);
        if let Some(width) = width {
            if let Some(iw) = init_width
                && iw != width
            {
                Err(PyRuntimeError::new_err(format!(
                    "Width of init expression ({iw}) does not match width of {name} ({width})"
                )))
            } else if let Some(nw) = next_width
                && nw != width
            {
                Err(PyRuntimeError::new_err(format!(
                    "Width of next expression ({nw}) does not match width of {name} ({width})"
                )))
            } else {
                let symbol = ctx.bv_symbol(name, width);
                let state = patronus::system::State {
                    symbol,
                    init: init.map(|i| i.0),
                    next: next.map(|n| n.0),
                };
                Ok(Self(state))
            }
        } else {
            Err(PyRuntimeError::new_err("No width provided!"))
        }
    }

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
        self.0.next.map(ExprRef)
    }

    #[getter]
    fn init(&self) -> Option<ExprRef> {
        self.0.init.map(ExprRef)
    }
}

#[pyclass]
pub struct TransitionSystem(patronus::system::TransitionSystem);

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
        Self(patronus::system::TransitionSystem {
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

    fn add_input(&mut self, symbol: ExprRef) -> PyResult<()> {
        let is_symbol = ContextGuardRead::default().deref()[symbol.0].is_symbol();
        if !is_symbol {
            Err(PyRuntimeError::new_err(format!(
                "{} is not a symbol",
                symbol.__str__()
            )))
        } else {
            self.0.inputs.push(symbol.0);
            Ok(())
        }
    }

    #[getter]
    fn outputs(&self) -> Vec<Output> {
        self.0.outputs.iter().map(|e| Output(*e)).collect()
    }

    #[setter(outputs)]
    fn set_outputs(&mut self, outputs: Vec<Output>) {
        self.0.outputs = outputs.into_iter().map(|e| e.0).collect();
    }

    fn add_output(&mut self, name: String, expr: ExprRef) {
        let name_id = ContextGuardWrite::default().deref_mut().string(name.into());
        self.0.outputs.push(patronus::system::Output {
            name: name_id,
            expr: expr.0,
        });
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

    fn add_bad_state(&mut self, name: String, expr: ExprRef) {
        self.0.bad_states.push(expr.0);
        let name_id = ContextGuardWrite::default().deref_mut().string(name.into());
        self.0.names[expr.0] = Some(name_id);
    }

    fn add_assertion(&mut self, name: &str, expr: ExprRef) {
        let not_name = format!("not_{name}");
        let not_expr = ContextGuardWrite::default().deref_mut().not(expr.0);
        self.add_bad_state(not_name, ExprRef(not_expr));
    }

    #[setter(bad_states)]
    fn set_bad_states(&mut self, bad_states: Vec<ExprRef>) {
        self.0.bad_states = bad_states.into_iter().map(|e| e.0).collect();
    }

    #[getter]
    fn constraints(&self) -> Vec<ExprRef> {
        self.0.constraints.iter().map(|e| ExprRef(*e)).collect()
    }

    #[setter(constraints)]
    fn set_constraints(&mut self, constraints: Vec<ExprRef>) {
        self.0.constraints = constraints.into_iter().map(|e| e.0).collect();
    }

    fn add_constraint(&mut self, name: String, expr: ExprRef) {
        self.0.constraints.push(expr.0);
        let name_id = ContextGuardWrite::default().deref_mut().string(name.into());
        self.0.names[expr.0] = Some(name_id);
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

    fn to_btor2_str(&self) -> String {
        btor2::serialize_to_str(ContextGuardRead::default().deref(), &self.0)
    }
}

#[pyfunction]
#[pyo3(signature = (content, name=None))]
pub fn parse_btor2_str(content: &str, name: Option<&str>) -> PyResult<TransitionSystem> {
    let mut ctx_guard = ContextGuardWrite::default();
    let ctx = ctx_guard.deref_mut();
    match btor2::parse_str(ctx, content, name) {
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
#[pyo3(name = "pypatronus")]
fn pypatronus(_py: Python<'_>, m: &pyo3::Bound<'_, pyo3::types::PyModule>) -> PyResult<()> {
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
    m.add_function(wrap_pyfunction!(simplify, m)?)?;
    m.add_function(wrap_pyfunction!(zext, m)?)?;
    m.add_function(wrap_pyfunction!(sext, m)?)?;
    m.add_function(wrap_pyfunction!(extract, m)?)?;
    m.add_function(wrap_pyfunction!(slice, m)?)?;
    // smt
    m.add_function(wrap_pyfunction!(solver, m)?)?;
    m.add_function(wrap_pyfunction!(parse_smtlib_expr, m)?)?;
    // mc
    m.add_class::<SmtModelChecker>()?;
    m.add_class::<ModelCheckResult>()?;
    Ok(())
}
