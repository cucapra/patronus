// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ctx::ContextGuardWrite;
use crate::smt::{convert_smt_err, name_to_solver};
use crate::{Model, TransitionSystem};
use patronus::smt::Solver;
use pyo3::prelude::*;
use std::fs::File;

#[pyfunction]
#[pyo3(signature = (solver, sys, k_max, check_constraints=true, check_bad_states_individually=false, smt_replay=None))]
pub fn bmc(
    solver: &str,
    sys: &TransitionSystem,
    k_max: u64,
    check_constraints: bool,
    check_bad_states_individually: bool,
    smt_replay: Option<&str>,
) -> PyResult<ModelCheckResult> {
    let solver = name_to_solver(solver)?;
    let dump_file = if let Some(path) = smt_replay {
        Some(File::create(path)?)
    } else {
        None
    };
    let mut smt_ctx = solver.start(dump_file).map_err(convert_smt_err)?;
    let res = patronus::mc::bmc(
        ContextGuardWrite::default().deref_mut(),
        &mut smt_ctx,
        &sys.0,
        check_constraints,
        check_bad_states_individually,
        k_max,
    );
    res.map(ModelCheckResult).map_err(convert_smt_err)
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
            patronus::mc::ModelCheckResult::Fail(_w) => {
                todo!()
            }
        }
    }

    #[getter]
    fn inputs(&self) -> Vec<Model> {
        todo!()
    }
}
