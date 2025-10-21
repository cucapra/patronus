// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ExprRef;
use crate::ctx::{ContextGuardRead, ContextGuardWrite};
use baa::{BitVecOps, Value};
use num_bigint::BigInt;
use patronus::expr::{Context, TypeCheck};
use patronus::mc::get_smt_value;
use patronus::smt::*;
use pyo3::exceptions::PyRuntimeError;
use pyo3::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};

#[pyclass]
pub struct SolverCtx {
    underlying: SmtLibSolverCtx,
    declared_symbols: Vec<FxHashMap<String, patronus::expr::ExprRef>>,
}

impl SolverCtx {
    fn new(underlying: SmtLibSolverCtx) -> Self {
        Self {
            underlying,
            declared_symbols: vec![FxHashMap::default()],
        }
    }

    fn symbol_by_name(&self, name: &str) -> Option<patronus::expr::ExprRef> {
        // from inner to outer
        for map in self.declared_symbols.iter().rev() {
            if let Some(symbol) = map.get(name) {
                return Some(*symbol);
            }
        }
        None
    }
}

fn find_symbols(ctx: &Context, e: patronus::expr::ExprRef) -> FxHashSet<patronus::expr::ExprRef> {
    let mut out = FxHashSet::default();
    patronus::expr::traversal::bottom_up(ctx, e, |ctx, e, _| {
        if ctx[e].is_symbol() {
            out.insert(e);
        }
    });
    out
}

#[pymethods]
impl SolverCtx {
    #[pyo3(signature = (*assertions))]
    fn check(&mut self, assertions: Vec<ExprRef>) -> PyResult<CheckSatResult> {
        if !assertions.is_empty() {
            self.push()?;
            for a in assertions.iter() {
                self.add(*a)?;
            }
        }
        let r = self
            .underlying
            .check_sat()
            .map(CheckSatResult)
            .map_err(convert_smt_err)?;
        if !assertions.is_empty() {
            self.pop()?;
        }
        Ok(r)
    }

    fn push(&mut self) -> PyResult<()> {
        self.underlying.push().map_err(convert_smt_err)?;
        self.declared_symbols.push(FxHashMap::default());
        Ok(())
    }

    fn pop(&mut self) -> PyResult<()> {
        self.underlying.pop().map_err(convert_smt_err)?;
        self.declared_symbols.pop();
        Ok(())
    }

    fn add(&mut self, assertion: ExprRef) -> PyResult<()> {
        let ctx_guard = ContextGuardRead::default();
        let ctx = ctx_guard.deref();
        let a = assertion.0;
        // scan the expression for any unknown symbols and declare them
        let symbols = find_symbols(ctx, a);
        for symbol in symbols.into_iter() {
            let tpe = ctx[symbol].get_type(ctx);
            let name = ctx[symbol].get_symbol_name(ctx).unwrap();
            if let Some(existing) = self.symbol_by_name(name) {
                // check for compatible type for existing symbols
                let existing_tpe = ctx[existing].get_type(ctx);
                if existing_tpe != tpe {
                    return Err(PyRuntimeError::new_err(format!(
                        "There is already a symbol `{name}` with incompatible type {existing_tpe} != {tpe}"
                    )));
                }
            } else {
                // declare if symbol does not exist
                self.underlying
                    .declare_const(ctx, symbol)
                    .map_err(convert_smt_err)?;
                self.declared_symbols
                    .last_mut()
                    .unwrap()
                    .insert(name.to_string(), symbol);
            }
        }

        self.underlying.assert(ctx, a).map_err(convert_smt_err)?;
        Ok(())
    }

    fn model(&mut self) -> PyResult<Model> {
        let mut ctx_guard = ContextGuardWrite::default();
        let ctx = ctx_guard.deref_mut();
        let mut entries = vec![];
        for s in self.declared_symbols.iter().flat_map(|m| m.values()) {
            let value = get_smt_value(ctx, &mut self.underlying, *s).map_err(convert_smt_err)?;
            entries.push((*s, value));
        }
        Ok(Model(entries))
    }
}

#[pyclass]
pub struct Model(Vec<(patronus::expr::ExprRef, Value)>);

#[pymethods]
impl Model {
    fn __str__(&self) -> String {
        "TODO".to_string()
    }

    fn __len__(&self) -> usize {
        self.0.len()
    }

    fn __getitem__(&self, symbol: ExprRef) -> Option<BigInt> {
        self.0
            .iter()
            .find(|(e, _)| *e == symbol.0)
            .map(|(_, value)| match value {
                Value::Array(_) => {
                    todo!("Array support!")
                }
                Value::BitVec(bv) => bv.to_big_int(),
            })
    }
}

#[pyclass]
pub struct CheckSatResult(CheckSatResponse);

#[pymethods]
impl CheckSatResult {
    fn __str__(&self) -> String {
        match self.0 {
            CheckSatResponse::Sat => "sat".to_string(),
            CheckSatResponse::Unsat => "unsat".to_string(),
            CheckSatResponse::Unknown => "unknonw".to_string(),
        }
    }
}

#[pyfunction]
#[pyo3(name = "Solver")]
pub fn solver(name: &str) -> PyResult<SolverCtx> {
    let solver = name_to_solver(name)?;
    Ok(SolverCtx::new(solver.start(None).map_err(convert_smt_err)?))
}

pub(crate) fn name_to_solver(name: &str) -> PyResult<SmtLibSolver> {
    match name.to_ascii_lowercase().as_str() {
        "z3" => Ok(Z3),
        "bitwuzla" => Ok(BITWUZLA),
        "yices" | "yices2" | "yices2-smt" => Ok(YICES2),
        _ => Err(PyRuntimeError::new_err(format!(
            "Unknonw or unsupported solver: {name}"
        ))),
    }
}

#[pyfunction]
#[pyo3(signature = (value, symbols=None))]
pub fn parse_smtlib_expr(
    value: &str,
    symbols: Option<FxHashMap<String, ExprRef>>,
) -> PyResult<ExprRef> {
    let symbols = symbols
        .unwrap_or_default()
        .into_iter()
        .map(|(k, v)| (k, v.0))
        .collect();
    parse_expr(
        ContextGuardWrite::default().deref_mut(),
        &symbols,
        value.as_bytes(),
    )
    .map_err(convert_smt_parse_err)
    .map(ExprRef)
}

pub(crate) fn convert_smt_err(e: Error) -> PyErr {
    PyRuntimeError::new_err(format!("smt: {e}"))
}

fn convert_smt_parse_err(e: SmtParserError) -> PyErr {
    PyRuntimeError::new_err(format!("smt: {e}"))
}
