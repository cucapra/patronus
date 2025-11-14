// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use std::fmt::Debug;
use std::hash::Hash;
use std::num::NonZeroU16;
use std::ops::Index;
use rustc_hash::FxHashMap;
use crate::expr::ExprRef;


#[derive(Debug, Clone)]
struct Auto<K: ActionKind>  {
    states: Vec<State<K>>,
}


#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct StateId(NonZeroU16);

impl StateId {
    fn from_index(index: usize) -> Self {
        Self(NonZeroU16::new(index as u16 + 1).unwrap())
    }

    fn index(&self) -> usize {
        (self.0.get() - 1) as usize
    }
}

impl<K: ActionKind> Index<StateId> for Auto<K> {
    type Output = State<K>;

    fn index(&self, index: StateId) -> &Self::Output {
        &self.states[index.index()]
    }
}

impl<K: ActionKind>  Auto<K> {
    /// Returns true iff all edges in this automaton are steps.
    fn is_sync(&self) -> bool {
        self.states.iter().all(|s| s.edges.iter().all(|e| e.is_step))
    }

    /// Remove all unreachable state.
    fn gc(&mut self) {
        let reachable = self.reachable_states();
        if reachable.len() < self.states.len() {
            let map = FxHashMap::from_iter(reachable.into_iter().enumerate().map(|(new, old)| (old, StateId::from_index(new))));
            todo!()

        }
    }

    fn reachable_states(&self) -> Vec<StateId> {
        todo!()
    }
}


#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct State<K: ActionKind>  {
    /// outgoing edges
    edges: Vec<Edge>,
    /// actions in this state
    actions: Vec<Action<K>>,
}



#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct Edge {
    dst: StateId,
    guard: ExprRef,
    is_step: bool,
}

trait ActionKind : Debug + Clone + Eq + Hash {}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct Action<K: ActionKind> {
    guard: ExprRef,
    kind: K,
}


/// builds a new version of the automaton where all edges are steps
fn with_only_steps<K: ActionKind>(a: &Auto<K>) -> Auto<K> {
    let done = a.states.iter().all(|s| s.edges.iter().all(|e| e.is_step));
    if done {
        a.clone()
    } else {
        let mut converted = vec![false; a.states.len()];
        let mut todo = vec![0];
        // TODO: how do we deal with new ids?
        while let Some()
        todo!()
    }

}