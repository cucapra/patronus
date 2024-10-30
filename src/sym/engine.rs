// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ir::{Context, TransitionSystem};

/// Symbolic execution engine.
#[allow(dead_code)]
pub struct SymEngine {
    sys: TransitionSystem,
}

impl SymEngine {
    pub fn new(ctx: &Context, sys: TransitionSystem) -> Self {
        Self { sys }
    }
}
