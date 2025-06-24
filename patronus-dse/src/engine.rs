// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::value_summary::Value;
use crate::{GuardCtx, ValueSummary};
use patronus::expr::{Context, ExprRef, Type, TypeCheck};
use patronus::sim::InitKind;
use patronus::system::analysis::count_expr_uses;
use patronus::system::TransitionSystem;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::ops::Index;

/// Symbolic execution engine.
pub struct SymEngine<V: Value> {
    sys: TransitionSystem,
    gc: GuardCtx,
    step_count: u64,
    data: Data<V>,
    dependencies: Dependencies,
}

impl<V: Value> SymEngine<V> {
    pub fn new(ctx: &Context, sys: TransitionSystem) -> Self {
        let dependencies = Dependencies::calculate(ctx, &sys);
        Self {
            sys,
            gc: GuardCtx::default(),
            step_count: 0,
            data: Data::<V>::default(),
            dependencies,
        }
    }

    /// Initializes all states and inputs to zero or random values.
    pub fn init(&mut self, ec: &mut Context, kind: InitKind) {
        // remove anything we have computed so far.
        self.data.clear();
        match kind {
            InitKind::Zero => {
                let symbols = self
                    .sys
                    .states
                    .iter()
                    .filter(|s| s.init.is_none())
                    .map(|s| s.symbol)
                    .chain(self.sys.inputs.iter().cloned());
                for sym in symbols {
                    let tpe = sym.get_type(ec);
                    let zero = V::zero(ec, &tpe);
                    self.data.set(sym, 0, ValueSummary::new(&mut self.gc, zero));
                }
            }
            InitKind::Random(_) => {
                todo!("add support for random initialization")
            }
        }
    }

    pub fn step(&mut self) {
        todo!()
    }

    pub fn set<'b>(&mut self, expr: ExprRef, value: ValueSummary<V>) {
        todo!()
    }

    pub fn get(&self, expr: ExprRef) -> ValueSummary<V> {
        let mut todo: SmallVec<[Dep; 4]> =
            SmallVec::from_iter(self.dependencies[expr].iter().cloned());
        while let Some(dep) = todo.pop() {}
        todo!("Where should we actually do the computation? As part of data or here?")
        //self.data.g
    }

    pub fn step_count(&self) -> u64 {
        self.step_count
    }
}

/// Key to a symbolic value
#[derive(Debug, Hash, Eq, PartialEq)]
struct Key {
    step: u32,
    expr: ExprRef,
}

/// Contains the symbolic values
struct Data<V: Value> {
    data: FxHashMap<Key, ValueSummary<V>>,
}

impl<V: Value> Data<V> {
    fn set(&mut self, expr: ExprRef, step: u32, value: ValueSummary<V>) {
        self.data.insert(Key { step, expr }, value);
    }

    fn get(&self, expr: ExprRef, step: u32) -> Option<&ValueSummary<V>> {
        self.data.get(&Key { step, expr })
    }

    fn clear(&mut self) {
        self.data.clear();
    }

    fn invalidate_dependents(&mut self, expr: ExprRef, step: u32) {
        todo!()
    }
}

impl<V: Value> Default for Data<V> {
    fn default() -> Self {
        Self {
            data: FxHashMap::default(),
        }
    }
}

/// Data structure, tracking the dependencies of every expression in the circuit.
struct Dependencies {}

impl Dependencies {
    fn calculate(ctx: &Context, sys: &TransitionSystem) -> Self {
        let uses = count_expr_uses(ctx, sys);

        todo!()
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
enum Dep {
    Same(ExprRef),
    Past(ExprRef),
}

impl Index<ExprRef> for Dependencies {
    type Output = [Dep];

    fn index(&self, index: ExprRef) -> &Self::Output {
        todo!()
    }
}
