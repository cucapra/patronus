// Copyright 2026 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Induction

use crate::expr::Context;
use crate::smt::SolverContext;
use crate::system::TransitionSystem;

/// Performs "0-induction", i.e. checks if bad states are reachable in an unconstraint state.
fn k_0_induction(ctx: &mut Context, smt_ctx: &mut impl SolverContext, sys: &TransitionSystem) {}
