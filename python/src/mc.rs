// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ctx::{ContextGuardRead, ContextGuardWrite};
use crate::smt::{convert_smt_err, name_to_solver};
use crate::{ExprRef, TransitionSystem};
use patronus::smt::SmtLibSolver;
use pyo3::exceptions::PyRuntimeError;
use pyo3::prelude::*;
use std::fs::File;

#[pyclass]
pub struct SmtModelChecker(::patronus::mc::SmtModelChecker<SmtLibSolver>);

#[pyclass]
pub struct ModelCheckResult(::patronus::mc::ModelCheckResult);

#[pymethods]
impl SmtModelChecker {
    #[new]
    #[pyo3(signature = (solver, check_constraints=true, check_bad_states_individually=false, save_smt_replay=false))]
    fn create(
        solver: &str,
        check_constraints: bool,
        check_bad_states_individually: bool,
        save_smt_replay: bool,
    ) -> PyResult<Self> {
        let solver = name_to_solver(solver)?;
        let opts = patronus::mc::SmtModelCheckerOptions {
            check_constraints,
            check_bad_states_individually,
            save_smt_replay,
        };
        let checker = patronus::mc::SmtModelChecker::new(solver, opts);
        Ok(Self(checker))
    }

    fn check(&self, sys: &TransitionSystem, k_max: u64) -> PyResult<ModelCheckResult> {
        Err(PyRuntimeError::new_err("TODO"))
        // self.0.check(ContextGuardWrite::default().deref_mut(), &sys.0, k_max).map(ModelCheckResult).map_err(convert_smt_err)
    }
}
