// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Expression Traversals
//!
//! Contains functions to simplify non-recursive implementations of expression traversals.

use crate::expr::{Context, Expr, ExprRef, ForEachChild};

/// Visits expression nodes bottom up while propagating values
#[inline]
pub fn bottom_up<R>(
    ctx: &Context,
    expr: ExprRef,
    f: impl FnMut(&Context, ExprRef, &[R]) -> R,
) -> R {
    bottom_up_multi_pat(
        ctx,
        expr,
        |_ctx, expr, children| expr.for_each_child(|c| children.push(*c)),
        f,
    )
}

/// Visits expression nodes bottom up while propagating values and mutating the context.
#[inline]
pub fn bottom_up_mut<R>(
    ctx: &mut Context,
    expr: ExprRef,
    f: impl FnMut(&mut Context, ExprRef, &[R]) -> R,
) -> R {
    bottom_up_multi_pat_mut(
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
    mut f: impl FnMut(&Context, ExprRef, &[R]) -> R,
) -> R {
    let mut todo = vec![(expr, false)];
    let mut stack = Vec::with_capacity(4);
    let mut child_vec = Vec::with_capacity(4);

    while let Some((e, bottom_up)) = todo.pop() {
        let expr = &ctx[e];

        // Check if there are children that we need to compute first.
        if !bottom_up {
            // check if there are child expressions to evaluate
            debug_assert!(child_vec.is_empty());
            get_children(ctx, expr, &mut child_vec);
            if !child_vec.is_empty() {
                todo.push((e, true));
                for c in child_vec.drain(..).rev() {
                    todo.push((c, false));
                }
                continue;
            }
        }

        // Otherwise, all arguments are available on the stack for us to use.
        let num_children = expr.num_children();
        let values = &stack[stack.len() - num_children..];
        let result = f(ctx, e, values);
        stack.truncate(stack.len() - num_children);
        stack.push(result);
    }

    debug_assert_eq!(stack.len(), 1);
    stack.pop().unwrap()
}

/// Visits expression nodes bottom up while propagating values and mutating the context.
/// Can match patterns with multiple nodes that will turn into a single output value.
#[inline]
pub fn bottom_up_multi_pat_mut<R>(
    ctx: &mut Context,
    expr: ExprRef,
    mut get_children: impl FnMut(&Context, &Expr, &mut Vec<ExprRef>),
    mut f: impl FnMut(&mut Context, ExprRef, &[R]) -> R,
) -> R {
    let mut todo = vec![(expr, false)];
    let mut stack = Vec::with_capacity(4);
    let mut child_vec = Vec::with_capacity(4);

    while let Some((e, bottom_up)) = todo.pop() {
        let expr = &ctx[e];

        // Check if there are children that we need to compute first.
        if !bottom_up {
            // check if there are child expressions to evaluate
            debug_assert!(child_vec.is_empty());
            get_children(ctx, expr, &mut child_vec);
            if !child_vec.is_empty() {
                todo.push((e, true));
                for c in child_vec.drain(..).rev() {
                    todo.push((c, false));
                }
                continue;
            }
        }

        // Otherwise, all arguments are available on the stack for us to use.
        let num_children = expr.num_children();
        let values = &stack[stack.len() - num_children..];
        let result = f(ctx, e, values);
        stack.truncate(stack.len() - num_children);
        stack.push(result);
    }

    debug_assert_eq!(stack.len(), 1);
    stack.pop().unwrap()
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TraversalCmd {
    Stop,
    Continue,
}

/// Visits expression from top to bottom. Halts exploration if a false is returned.
#[inline]
pub fn top_down(
    ctx: &Context,
    expr: ExprRef,
    mut f: impl FnMut(&Context, ExprRef) -> TraversalCmd,
) {
    let mut todo = vec![expr];
    while let Some(e) = todo.pop() {
        let do_continue = f(ctx, e) == TraversalCmd::Continue;
        if do_continue {
            ctx[e].for_each_child(|&c| todo.push(c));
        }
    }
}
