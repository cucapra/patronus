// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ir::{Context, Expr, ExprRef, ForEachChild};

/// Visits expression nodes bottom up while propagating values
#[inline]
pub fn bottom_up<R>(ctx: &Context, expr: ExprRef, f: impl FnMut(&Context, &Expr, &[R]) -> R) -> R {
    bottom_up_multi_pat(
        ctx,
        expr,
        |_ctx, expr, children| expr.for_each_child(|c| children.push(*c)),
        f,
    )
}

/// Visits expression nodes bottom up while propagating values.
/// Can match patterns with multiple nodes that will turn into a single output value.
#[inline]
pub fn bottom_up_multi_pat<R>(
    ctx: &Context,
    expr: ExprRef,
    mut get_children: impl FnMut(&Context, &Expr, &mut Vec<ExprRef>),
    mut f: impl FnMut(&Context, &Expr, &[R]) -> R,
) -> R {
    let mut todo = vec![(expr, false)];
    let mut stack = Vec::with_capacity(4);
    let mut child_vec = Vec::with_capacity(4);

    while let Some((e, bottom_up)) = todo.pop() {
        let expr = ctx.get(e);

        // Check if there are children that we need to compute first.
        if !bottom_up {
            // check if there are child expressions to evaluate
            debug_assert!(child_vec.is_empty());
            get_children(ctx, expr, &mut child_vec);
            if !child_vec.is_empty() {
                todo.push((e, true));
                for c in child_vec.drain(..) {
                    todo.push((c, false));
                }
                continue;
            }
        }

        // Otherwise, all arguments are available on the stack for us to use.
        let num_children = expr.num_children();
        let values = &stack[stack.len() - num_children..];
        let result = f(ctx, expr, values);
        stack.truncate(stack.len() - num_children);
        stack.push(result);
    }

    debug_assert_eq!(stack.len(), 1);
    stack.pop().unwrap()
}
