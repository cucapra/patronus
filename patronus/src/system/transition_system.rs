// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::expr::{Context, ExprMap, ExprRef, SparseExprMap, StringRef};
use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
pub struct State {
    pub symbol: ExprRef,
    pub init: Option<ExprRef>,
    pub next: Option<ExprRef>,
}

impl State {
    pub fn is_const(&self) -> bool {
        self.next.map(|n| n == self.symbol).unwrap_or(false)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct StateRef(usize);

impl StateRef {
    pub fn to_index(&self) -> usize {
        self.0
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct InputRef(usize);

#[derive(Debug, Clone, Copy)]
pub struct Output {
    pub name: StringRef,
    pub expr: ExprRef,
}

#[derive(Debug, Clone)]
pub struct TransitionSystem {
    pub name: String,
    pub states: Vec<State>,
    pub inputs: Vec<ExprRef>,
    pub outputs: Vec<Output>,
    pub bad_states: Vec<ExprRef>,
    pub constraints: Vec<ExprRef>,
    pub names: SparseExprMap<Option<StringRef>>,
}

impl TransitionSystem {
    pub fn new(name: String) -> Self {
        TransitionSystem {
            name,
            states: Vec::default(),
            inputs: Vec::default(),
            outputs: Vec::default(),
            bad_states: Vec::default(),
            constraints: Vec::default(),
            names: SparseExprMap::default(),
        }
    }

    pub fn get_state(&self, reference: StateRef) -> &State {
        &self.states[reference.0]
    }

    pub fn update_signal_name(&mut self, old: ExprRef, new: ExprRef) {
        if old != new {
            if let Some(old_name) = self.names[old] {
                if self.names[new].is_none() {
                    self.names[new] = Some(old_name);
                    self.names[old] = None;
                }
            }
        }
    }

    pub fn add_input(&mut self, ctx: &Context, symbol: ExprRef) {
        assert!(ctx[symbol].is_symbol());
        let name = ctx[symbol].get_symbol_name_ref();
        self.inputs.push(symbol);
        self.names[symbol] = name;
    }

    pub fn add_output(&mut self, ctx: &mut Context, name: std::borrow::Cow<str>, expr: ExprRef) {
        let name = ctx.string(name);
        self.outputs.push(Output { name, expr });
    }

    pub fn add_state(&mut self, ctx: &Context, state: impl Into<State>) -> StateRef {
        let state = state.into();
        assert!(ctx[state.symbol].is_symbol());
        // also add as a signal
        let name = ctx[state.symbol].get_symbol_name_ref();
        self.names[state.symbol] = name;
        let id = self.states.len();
        self.states.push(state);
        StateRef(id)
    }

    pub fn get_state_by_name(&self, ctx: &Context, name: &str) -> Option<&State> {
        self.states
            .iter()
            .find(|s| ctx.get_symbol_name(s.symbol).unwrap() == name)
    }

    pub fn modify_state<F>(&mut self, reference: StateRef, modify: F)
    where
        F: FnOnce(&mut State),
    {
        modify(self.states.get_mut(reference.0).unwrap())
    }

    pub fn state_map(&self) -> FxHashMap<ExprRef, &State> {
        FxHashMap::from_iter(self.states.iter().map(|s| (s.symbol, s)))
    }

    pub fn input_set(&self) -> FxHashSet<ExprRef> {
        FxHashSet::from_iter(self.inputs.iter().cloned())
    }

    /// Update all output, input, assume, assert, state expressions.
    /// If `update` returns `None`, no update is performed.
    pub fn update_expressions(&mut self, mut update: impl FnMut(ExprRef) -> Option<ExprRef>) {
        for old in self.inputs.iter_mut() {
            *old = update(*old).unwrap_or(*old);
        }
        for old in self.constraints.iter_mut() {
            *old = update(*old).unwrap_or(*old);
        }
        for old in self.bad_states.iter_mut() {
            *old = update(*old).unwrap_or(*old);
        }
        for output in self.outputs.iter_mut() {
            output.expr = update(output.expr).unwrap_or(output.expr);
        }
        for state in self.states.iter_mut() {
            state.symbol = update(state.symbol).unwrap_or(state.symbol);
            state.init = state.init.and_then(&mut update);
            state.next = state.next.and_then(&mut update);
        }

        // update names
        let old_name_exprs = self.names.non_default_value_keys().collect::<Vec<_>>();
        for old_expr in old_name_exprs.into_iter() {
            if let Some(new_expr) = update(old_expr) {
                if new_expr != old_expr {
                    self.names[new_expr] = self.names[old_expr];
                }
            }
        }
    }

    /// Returns a list of all assume and assert expressions.
    pub fn get_assert_assume_exprs(&self) -> Vec<ExprRef> {
        let mut out = Vec::with_capacity(self.bad_states.len() + self.constraints.len());
        out.extend_from_slice(self.bad_states.as_slice());
        out.extend_from_slice(self.constraints.as_slice());
        out
    }

    /// Returns a list of all assume, assert and output expressions.
    pub fn get_assert_assume_output_exprs(&self) -> Vec<ExprRef> {
        let mut out =
            Vec::with_capacity(self.outputs.len() + self.bad_states.len() + self.constraints.len());
        out.extend(self.outputs.iter().map(|o| o.expr));
        out.extend_from_slice(self.bad_states.as_slice());
        out.extend_from_slice(self.constraints.as_slice());
        out
    }

    /// Returns a list of all state init expressions.
    pub fn get_init_exprs(&self) -> Vec<ExprRef> {
        Vec::from_iter(self.states.iter().flat_map(|s| s.init))
    }

    /// Returns a list of all state next expressions.
    pub fn get_next_exprs(&self) -> Vec<ExprRef> {
        Vec::from_iter(self.states.iter().flat_map(|s| s.next))
    }

    /// Returns a list of all output, input, assume, assert and state expressions.
    pub fn get_all_exprs(&self) -> Vec<ExprRef> {
        // include all input, output, assertion and assumptions expressions
        let mut out = vec![];
        out.extend_from_slice(self.inputs.as_slice());
        out.extend(self.outputs.iter().map(|o| o.expr));
        out.extend_from_slice(self.bad_states.as_slice());
        out.extend_from_slice(self.constraints.as_slice());

        // include all states
        for state in self.states.iter() {
            out.push(state.symbol);
            if let Some(init) = state.init {
                out.push(init);
            }
            if let Some(next) = state.next {
                out.push(next);
            }
        }

        out
    }

    /// Creates a map from signal name to expression
    pub fn get_name_map(&self, ctx: &Context) -> FxHashMap<String, ExprRef> {
        let mut m = FxHashMap::default();
        for out in self.outputs.iter() {
            m.insert(ctx[out.name].to_string(), out.expr);
        }
        for &e in self
            .bad_states
            .iter()
            .chain(self.constraints.iter())
            .chain(self.inputs.iter())
            .chain(self.states.iter().map(|s| &s.symbol))
        {
            if let Some(name) = ctx[e].get_symbol_name(ctx) {
                m.insert(name.to_string(), e);
            }
            if let Some(name) = self.names[e] {
                m.insert(ctx[name].to_string(), e);
            }
        }
        m
    }

    /// Returns input by name.
    pub fn lookup_input(&self, ctx: &Context, name: &str) -> Option<ExprRef> {
        self.inputs
            .iter()
            .find(|&&i| {
                ctx[i]
                    .get_symbol_name(ctx)
                    .map(|i_name| i_name == name)
                    .unwrap_or(false)
            })
            .cloned()
    }

    /// Returns output by name.
    pub fn lookup_output(&self, ctx: &Context, name: &str) -> Option<ExprRef> {
        self.outputs
            .iter()
            .find(|&&o| ctx[o.name] == name)
            .map(|o| o.expr)
    }
}
