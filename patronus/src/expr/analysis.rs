// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024-2026 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::{Context, ExprMap, ExprRef, ForEachChild, SparseExprMap, traversal};
use rustc_hash::FxHashSet;

pub type UseCountInt = u16;

/// Counts how often expressions in the DAGs characterized by the provided roots are used.
pub fn count_expr_uses(ctx: &Context, roots: Vec<ExprRef>) -> impl ExprMap<UseCountInt> {
    let mut use_count = SparseExprMap::default();
    let mut todo = roots;

    // ensure that all roots start with count 1
    for expr in todo.iter() {
        use_count[*expr] = 1;
    }

    while let Some(expr) = todo.pop() {
        update_expr_child_uses(ctx, expr, &mut use_count, &mut todo);
    }

    use_count
}

/// Returns all symbols in the given expression.
pub fn find_symbols(ctx: &Context, e: ExprRef) -> FxHashSet<ExprRef> {
    let mut out = FxHashSet::default();
    traversal::bottom_up(ctx, e, |ctx, e, _| {
        if ctx[e].is_symbol() {
            out.insert(e);
        }
    });
    out
}

/// Increments the use counts for all children of the expression `expr` and
/// adds any child encountered for the first time to the `todo` list.
#[inline]
pub fn update_expr_child_uses(
    ctx: &Context,
    expr: ExprRef,
    use_count: &mut impl ExprMap<UseCountInt>,
    todo: &mut Vec<ExprRef>,
) {
    ctx[expr].for_each_child(|child| {
        let count = use_count[*child];
        let is_first_use = count == 0;
        use_count[*child] = count.saturating_add(1);
        if is_first_use {
            todo.push(*child);
        }
    });
}
