// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use pyo3::prelude::*;
use std::ops::{Deref, DerefMut};
use std::sync::{LazyLock, RwLock, RwLockReadGuard, RwLockWriteGuard};

/// Context that is used by default for all operations.
/// Python usage is expected to be less performance critical, so using a single global
/// context seems acceptable and will simplify use.
static DEFAULT_CONTEXT: LazyLock<RwLock<::patronus::expr::Context>> =
    LazyLock::new(|| RwLock::new(::patronus::expr::Context::default()));

/// Exposes the Context object to python
#[pyclass]
pub struct Context(::patronus::expr::Context);

pub(crate) enum ContextGuardWrite<'a> {
    // TODO: reintroduce local context support!
    // Local(&'a mut Context),
    Shared(RwLockWriteGuard<'a, ::patronus::expr::Context>),
}

// TODO: reintroduce local context support!
// impl<'a> From<Option<&'a mut Context>> for ContextGuardWrite<'a> {
//     fn from(value: Option<&'a mut Context>) -> Self {
//         value
//             .map(|ctx| Self::Local(ctx))
//             .unwrap_or_else(|| Self::Shared(DEFAULT_CONTEXT.write().unwrap()))
//     }
// }

impl<'a> Default for ContextGuardWrite<'a> {
    fn default() -> Self {
        Self::Shared(DEFAULT_CONTEXT.write().unwrap())
    }
}

impl<'a> ContextGuardWrite<'a> {
    pub fn deref_mut(&mut self) -> &mut ::patronus::expr::Context {
        match self {
            // TODO: reintroduce local context support!
            // Self::Local(ctx) => &mut ctx.0,
            Self::Shared(guard) => guard.deref_mut(),
        }
    }
}

pub(crate) enum ContextGuardRead<'a> {
    // TODO: reintroduce local context support!
    // Local(&'a Context),
    Shared(RwLockReadGuard<'a, ::patronus::expr::Context>),
}

// TODO: reintroduce local context support!
// impl<'a> From<Option<&'a mut Context>> for ContextGuardRead<'a> {
//     fn from(value: Option<&'a mut Context>) -> Self {
//         value
//             .map(|ctx| Self::Local(ctx))
//             .unwrap_or_else(|| Self::default())
//     }
// }

impl<'a> Default for ContextGuardRead<'a> {
    fn default() -> Self {
        Self::Shared(DEFAULT_CONTEXT.read().unwrap())
    }
}

impl<'a> ContextGuardRead<'a> {
    pub fn deref(&self) -> &::patronus::expr::Context {
        match self {
            // TODO: reintroduce local context support!
            // Self::Local(ctx) => &ctx.0,
            Self::Shared(guard) => guard.deref(),
        }
    }
}
