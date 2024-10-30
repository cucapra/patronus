// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ir::*;
use boolean_expression::{BDDFunc, BDD};
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

#[derive(Debug, Clone)]
pub struct GuardCtx {
    bdd: BDD<u16>,
}

impl Default for GuardCtx {
    fn default() -> Self {
        let bdd = BDD::new();
        Self { bdd }
    }
}

impl GuardCtx {
    pub fn tru(&mut self) -> Guard {
        self.bdd.constant(true)
    }

    pub fn and(&mut self, a: Guard, b: Guard) -> Guard {
        self.bdd.and(a, b)
    }

    pub fn or(&mut self, a: Guard, b: Guard) -> Guard {
        self.bdd.or(a, b)
    }

    /// guard can never be true
    pub fn is_unsat(&self, e: Guard) -> bool {
        !self.bdd.sat(e)
    }
}

type Guard = BDDFunc;

#[allow(dead_code)]
pub struct ValueSummary<V: Clone> {
    entries: Vec<Entry<V>>,
}

impl<V: Clone + Eq + Hash> ValueSummary<V> {
    pub fn new(gc: &mut GuardCtx, value: V) -> Self {
        Self {
            entries: vec![Entry {
                guard: gc.tru(),
                value,
            }],
        }
    }

    pub fn apply_bin_op(
        ec: &mut Context,
        gc: &mut GuardCtx,
        op: fn(a: V, b: V) -> V,
        a: Self,
        b: Self,
    ) -> Self {
        let mut a = a.entries;
        let mut b = b.entries;
        debug_assert!(!a.is_empty() && !b.is_empty());
        let mut out = Vec::with_capacity(a.len() + b.len());

        // first we check to see if any guards are the same, then we do not need to apply the cross product
        let a_guards: HashSet<Guard> = a.iter().map(|e| e.guard).collect();
        let b_guards: HashSet<Guard> = b.iter().map(|e| e.guard).collect();
        let common_guards: HashSet<Guard> = a_guards.intersection(&b_guards).cloned().collect();

        if !common_guards.is_empty() {
            // merge common guard entries
            let mut sorted_common_guards: Vec<Guard> = common_guards.iter().cloned().collect();
            sorted_common_guards.sort();
            for guard in sorted_common_guards.into_iter() {
                // unwrap should never fail, since otherwise this would not be a common guard!
                let a_expr = a.iter().find(|e| e.guard == guard).cloned().unwrap().value;
                let b_expr = b.iter().find(|e| e.guard == guard).cloned().unwrap().value;

                // we can create exactly one new entry with the common guard
                out.push(Entry {
                    guard,
                    value: op(a_expr, b_expr),
                })
            }

            // remove any entries that we already processed
            a.retain(|e| !common_guards.contains(&e.guard));
            b.retain(|e| !common_guards.contains(&e.guard));
        }

        // for any other guards, we need to consider all possible combinations
        if !a.is_empty() {
            debug_assert!(!b.is_empty(), "when a is empty, b should also be empty!");

            for a_entry in a.into_iter() {
                for b_entry in b.iter() {
                    let guard = gc.and(a_entry.guard, b_entry.guard);
                    if !gc.is_unsat(guard) {
                        // create a new entry
                        out.push(Entry {
                            guard,
                            value: op(a_entry.value.clone(), b_entry.value.clone()),
                        })
                    }
                }
            }
        }

        Self { entries: out }
    }

    /// Returns the number of entries in the value summary.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// combines entries with the same value into one
    fn coalesce(&mut self, gc: &mut GuardCtx) {
        let mut by_value = HashMap::with_capacity(self.entries.len());
        let mut delete_list = vec![];
        for ii in 0..self.entries.len() {
            let entry = self.entries[ii].clone();
            if let Some(prev_ii) = by_value.get(&entry.value) {
                // we found a duplicate! let's merge
                let prev_ii: usize = *prev_ii;
                let prev = self.entries[prev_ii].clone();
                let combined_guard = gc.or(prev.guard, entry.guard);
                // update the current entry
                self.entries[ii].guard = combined_guard;
                // schedule the duplicate to be deleted
                delete_list.push(prev_ii);
            }
            // remember the final entry containing this value
            by_value.insert(entry.value, ii);
        }

        // delete duplicate entries
        delete_entries(delete_list, &mut self.entries);
    }
}

fn delete_entries<T>(delete_list: Vec<usize>, entries: &mut Vec<T>) {
    if !delete_list.is_empty() {
        let mut delete_iter = delete_list.into_iter().peekable();
        let mut index = 0usize;
        entries.retain(|_| {
            let current_index = index;
            index += 1;
            if delete_iter.peek().cloned() == Some(current_index) {
                delete_iter.next().unwrap();
                false
            } else {
                true
            }
        })
    }
}

#[derive(Clone)]
struct Entry<V: Clone> {
    guard: Guard,
    value: V,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_value_summaries() {
        let mut ctx = Context::default();
        let mut gc = GuardCtx::default();

        let vs = ValueSummary::new(&mut gc, ctx.bv_symbol("a", 16));
        assert_eq!(vs.len(), 1);
    }

    #[test]
    fn test_delete_entries() {
        let mut entries = vec!['a', 'b', 'c', 'd'];
        delete_entries(vec![1, 2], &mut entries);
        assert_eq!(entries, ['a', 'd']);
    }
}
