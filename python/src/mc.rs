// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ctx::ContextGuardWrite;
use crate::smt::{convert_smt_err, name_to_solver};
use crate::{Model, TransitionSystem};
use patronus::smt::SmtLibSolver;
use pyo3::prelude::*;

#[pyclass]
pub struct SmtModelChecker(::patronus::mc::SmtModelChecker<SmtLibSolver>);

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
        let mut ctx_guard = ContextGuardWrite::default();
        let ctx = ctx_guard.deref_mut();
        self.0
            .check(ctx, &sys.0, k_max)
            .map(ModelCheckResult)
            .map_err(convert_smt_err)
    }
}

#[pyclass]
pub struct ModelCheckResult(::patronus::mc::ModelCheckResult);

#[pymethods]
impl ModelCheckResult {
    fn __str__(&self) -> String {
        match &self.0 {
            patronus::mc::ModelCheckResult::Success => "unsat".to_string(),
            patronus::mc::ModelCheckResult::Fail(_) => "sat".to_string(),
        }
    }

    fn __len__(&self) -> usize {
        match &self.0 {
            patronus::mc::ModelCheckResult::Success => 0,
            patronus::mc::ModelCheckResult::Fail(w) => w.inputs.len(),
        }
    }

    #[getter]
    fn inits(&self) -> Option<Model> {
        match &self.0 {
            patronus::mc::ModelCheckResult::Success => None,
            patronus::mc::ModelCheckResult::Fail(w) => {
                todo!()
            }
        }
    }

    #[getter]
    fn inputs(&self) -> Vec<Model> {
        todo!()
    }
}
