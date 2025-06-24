// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use boolean_expression::{BDDFunc, BDD};
use patronus::expr::*;
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};
use smallvec::{smallvec, Array, SmallVec};
use std::hash::Hash;

#[derive(Debug, Clone)]
pub struct GuardCtx {
    /// The variables in the BDD are expressions which we do not want to import into the BDD.
    bdd: BDD<ExprRef>,
}

impl Default for GuardCtx {
    fn default() -> Self {
        let bdd = BDD::new();
        Self { bdd }
    }
}

impl GuardCtx {
    pub fn get_true(&mut self) -> Guard {
        self.bdd.constant(true)
    }
    pub fn get_false(&mut self) -> Guard {
        self.bdd.constant(false)
    }

    pub fn and(&mut self, a: Guard, b: Guard) -> Guard {
        self.bdd.and(a, b)
    }

    pub fn or(&mut self, a: Guard, b: Guard) -> Guard {
        self.bdd.or(a, b)
    }

    pub fn not(&mut self, e: Guard) -> Guard {
        self.bdd.not(e)
    }

    /// guard can never be true
    pub fn is_false(&self, e: Guard) -> bool {
        matches!(e, boolean_expression::BDD_ZERO)
    }

    pub fn is_true(&self, e: Guard) -> bool {
        matches!(e, boolean_expression::BDD_ONE)
    }

    pub fn expr_to_guard(&mut self, ec: &Context, expr: ExprRef) -> Guard {
        debug_assert!(expr.is_bool(ec));
        traversal::bottom_up_multi_pat(
            ec,
            expr,
            |ctx, expr, children| {
                // check to see if we are going to convert this expression, if we are not, then
                // we do not want to visit the children at all
                expr.for_each_child(|c| children.push(*c));
                let all_bool_children = children.iter().all(|e| ctx[*e].is_bool(ctx));
                if !all_bool_children {
                    children.clear(); // we do not want to include the children
                }
            },
            |ctx, expr, children| {
                match &ctx[expr] {
                    Expr::BVLiteral(v) => self.bdd.constant(v.is_true()),
                    Expr::BVNot(_, _) => self.bdd.not(children[0]),
                    Expr::BVAnd(_, _, _) => self.bdd.and(children[0], children[1]),
                    Expr::BVOr(_, _, _) => self.bdd.or(children[0], children[1]),
                    Expr::BVXor(_, _, _) => self.bdd.xor(children[0], children[1]),
                    Expr::BVImplies(_, _) => self.bdd.implies(children[0], children[1]),
                    // other expressions just become a terminal
                    _ => {
                        debug_assert!(
                            children.is_empty(),
                            "children should not have been visited!"
                        );
                        self.bdd.terminal(expr)
                    }
                }
            },
        )
    }
}

type Guard = BDDFunc;

pub type ValueContext = Context;

/// Value in a `[[ValueSummary]]`.
pub trait Value: Clone + Eq + Hash {
    type Concrete;

    /// Indicates that the value is trivially true.
    fn is_true(&self, _ec: &ValueContext) -> bool {
        false
    }
    /// Indicates that the value is trivially false.
    fn is_false(&self, _ec: &ValueContext) -> bool {
        false
    }
    /// Returns the concrete value, iff available.
    fn concrete(&self, _ec: &ValueContext) -> Option<Self::Concrete>;
    /// Generate a zero value of the same type.
    fn zero(_ec: &mut ValueContext, tpe: &Type) -> Self;
}

type EntryVec<V: Value> = SmallVec<[Entry<V>; 4]>;

#[allow(dead_code)]
#[derive(Clone)]
pub struct ValueSummary<V: Value> {
    entries: EntryVec<V>,
}

impl<V: Value> ValueSummary<V> {
    pub fn new(gc: &mut GuardCtx, value: V) -> Self {
        Self {
            entries: smallvec![Entry {
                guard: gc.get_true(),
                value,
            }],
        }
    }

    /// Applies an operation to a and b.
    pub fn apply_bin_op(
        ec: &mut ValueContext,
        gc: &mut GuardCtx,
        op: fn(ec: &mut ValueContext, a: V, b: V) -> V,
        a: Self,
        b: Self,
    ) -> Self {
        let mut a = a.entries;
        let mut b = b.entries;
        debug_assert!(!a.is_empty() && !b.is_empty());
        let mut out = SmallVec::with_capacity(a.len() + b.len());

        // first we check to see if any guards are the same, then we do not need to apply the cross product
        let a_guards: FxHashSet<Guard> = a.iter().map(|e| e.guard).collect();
        let b_guards: FxHashSet<Guard> = b.iter().map(|e| e.guard).collect();
        let common_guards: FxHashSet<Guard> = a_guards.intersection(&b_guards).cloned().collect();

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
                    value: op(ec, a_expr, b_expr),
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
                    if !gc.is_false(guard) {
                        // create a new entry
                        out.push(Entry {
                            guard,
                            value: op(ec, a_entry.value.clone(), b_entry.value.clone()),
                        })
                    }
                }
            }
        }

        Self { entries: out }
    }

    /// Indicates that this value summary is trivially true.
    pub fn is_true(&self, ec: &ValueContext) -> bool {
        match self.entries.as_slice() {
            [entry] => entry.value.is_true(ec),
            _ => false,
        }
    }

    /// Indicates that this value summary is trivially false.
    pub fn is_false(&self, ec: &ValueContext) -> bool {
        match self.entries.as_slice() {
            [entry] => entry.value.is_false(ec),
            _ => false,
        }
    }

    /// Returns the number of entries in the value summary.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        debug_assert!(
            !self.entries.is_empty(),
            "in a valid ValueSummary there always must be at least one entry"
        );
        false
    }

    /// combines entries with the same value into one
    pub fn coalesce(&mut self, gc: &mut GuardCtx) {
        coalesce_entries(&mut self.entries, gc);
    }

    /// returns a concrete value, if the value summary consists of a single concrete value
    pub fn concrete(&self) -> Option<V::Concrete> {
        todo!()
    }
}

fn coalesce_entries<V: Value>(entries: &mut EntryVec<V>, gc: &mut GuardCtx) {
    let mut by_value = FxHashMap::with_capacity_and_hasher(entries.len(), FxBuildHasher);
    let mut delete_list = vec![];
    for ii in 0..entries.len() {
        let entry = entries[ii].clone();
        if let Some(prev_ii) = by_value.get(&entry.value) {
            // we found a duplicate! let's merge
            let prev_ii: usize = *prev_ii;
            let prev = entries[prev_ii].clone();
            let combined_guard = gc.or(prev.guard, entry.guard);
            // update the current entry
            entries[ii].guard = combined_guard;
            // schedule the duplicate to be deleted
            delete_list.push(prev_ii);
        }
        // remember the final entry containing this value
        by_value.insert(entry.value, ii);
    }

    // delete duplicate entries
    delete_entries(delete_list, entries);
}

impl<V: Value + ToGuard> ValueSummary<V> {
    /// Combines two values depending on a conditional.
    pub fn apply_ite(
        ec: &mut ValueContext,
        gc: &mut GuardCtx,
        cond: Self,
        tru: Self,
        fals: Self,
    ) -> Self {
        // is the condition trivially true?
        if cond.is_true(ec) {
            return tru;
        }
        if cond.is_false(ec) {
            return fals;
        }

        // lift condition values into a single guard
        let (tru_cond, entries) = cond.to_guard(ec, gc);
        if !entries.is_empty() {
            todo!("deal with special value entries!")
        }
        let fals_cond = gc.not(tru_cond);
        if gc.is_true(tru_cond) {
            return tru;
        }
        if gc.is_true(fals_cond) {
            return fals;
        }

        // create combined entries
        let mut entries = EntryVec::with_capacity(tru.len() + fals.len());
        for e in tru.entries.into_iter() {
            entries.push(Entry {
                guard: gc.and(e.guard, tru_cond),
                value: e.value,
            });
        }
        for e in fals.entries.into_iter() {
            entries.push(Entry {
                guard: gc.and(e.guard, fals_cond),
                value: e.value,
            });
        }

        // return combined value summary
        ValueSummary { entries }
    }

    /// Converts the value summary into a guard.
    fn to_guard(&self, ec: &mut ValueContext, gc: &mut GuardCtx) -> (Guard, EntryVec<V>) {
        let mut results = EntryVec::default();
        let mut guard = gc.get_false();
        for e in self.entries.iter() {
            match e.value.to_guard(ec, gc) {
                GuardResult::Guard(value_as_guard) => {
                    let combined = gc.and(e.guard, value_as_guard);
                    // add to global guard
                    guard = gc.or(guard, combined);
                }
                GuardResult::IteResult(value) => {
                    // we get a special value which will appear in the output under this condition
                    results.push(Entry {
                        guard: e.guard,
                        value,
                    });
                }
                GuardResult::CannotConvert => unreachable!("failed to convert"),
            }
        }
        // eagerly combine entries that evaluated to the same result
        // in the case of X/Unknown, this should leave us with a single entry
        if results.len() > 1 {
            coalesce_entries(&mut results, gc);
        }
        (guard, results)
    }

    /// Canonicalizes a boolean value summary such that it only contains two or fewer entries.
    pub fn import_into_guard(&mut self, ec: &mut ValueContext, gc: &mut GuardCtx) {
        let (value_as_guard, others) = self.to_guard(ec, gc);
        if gc.is_true(value_as_guard) {
            debug_assert!(others.is_empty());
            self.entries = smallvec![Entry {
                guard: gc.get_true(),
                value: V::true_value(ec),
            }];
            return;
        }
        if gc.is_false(value_as_guard) {
            debug_assert!(others.is_empty());
            self.entries = smallvec![Entry {
                guard: gc.get_true(),
                value: V::false_value(ec),
            }];
            return;
        }
        if !others.is_empty() {
            todo!("deal with other values!")
        }
        self.entries = smallvec![
            Entry {
                guard: gc.not(value_as_guard),
                value: V::false_value(ec),
            },
            Entry {
                guard: value_as_guard,
                value: V::true_value(ec),
            },
        ];
    }
}

fn delete_entries<T: Array>(
    delete_list: impl IntoIterator<Item = usize>,
    entries: &mut SmallVec<T>,
) {
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

/// Implemented by values that can be lifted into a guard.
pub trait ToGuard: Value {
    /// Indicates whether the given value can be turned into a guard.
    fn can_be_guard(&self, ec: &ValueContext) -> bool;

    /// Turns the value into a guard.
    fn to_guard(&self, ec: &ValueContext, gc: &mut GuardCtx) -> GuardResult<Self>;
    fn true_value(ec: &mut ValueContext) -> Self;
    fn false_value(ec: &mut ValueContext) -> Self;
}

pub enum GuardResult<V: Value> {
    /// Value converted to a guard.
    Guard(Guard),
    /// Cannot convert to a guard. Generally only happens if the program logic is faulty.
    CannotConvert,
    /// The result of the ITE under this condition will always be the value provided.
    IteResult(V),
}

impl Value for ExprRef {
    type Concrete = baa::Value;

    fn is_true(&self, ec: &ValueContext) -> bool {
        ec[*self].is_true()
    }

    fn is_false(&self, ec: &ValueContext) -> bool {
        ec[*self].is_false()
    }

    fn concrete(&self, ec: &ValueContext) -> Option<Self::Concrete> {
        todo!()
    }

    fn zero(ec: &mut ValueContext, tpe: &Type) -> Self {
        match *tpe {
            Type::BV(width) => ec.zero(width),
            Type::Array(t) => ec.zero_array(t),
        }
    }
}

impl ToGuard for ExprRef {
    fn can_be_guard(&self, ec: &ValueContext) -> bool {
        ec[*self].is_bool(ec)
    }

    fn to_guard(&self, ec: &Context, gc: &mut GuardCtx) -> GuardResult<Self> {
        if !self.can_be_guard(ec) {
            return GuardResult::CannotConvert;
        }
        let guard = gc.expr_to_guard(ec, *self);
        GuardResult::Guard(guard)
    }
    fn true_value(ec: &mut ValueContext) -> Self {
        ec.get_true()
    }

    fn false_value(ec: &mut ValueContext) -> Self {
        ec.get_false()
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
        let mut entries: SmallVec<[char; 4]> = smallvec!['a', 'b', 'c', 'd'];
        delete_entries(vec![1, 2], &mut entries);
        assert_eq!(entries.as_slice(), ['a', 'd']);
    }
}
