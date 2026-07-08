// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use super::TransitionSystem;
use crate::btor2::{DEFAULT_INPUT_PREFIX, DEFAULT_STATE_PREFIX};
use crate::expr::*;
use rustc_hash::FxHashMap;

/** Remove any inputs named `_input_[...]` and replace their use with a literal zero.
* This essentially gets rid of all undefined value modelling by yosys.
 */
pub fn replace_anonymous_inputs_with_zero(ctx: &mut Context, sys: &mut TransitionSystem) {
    // find and remove inputs
    let mut replace_map = FxHashMap::default();
    sys.inputs.retain(|&input| {
        let name = ctx.get_symbol_name(input).unwrap();
        if name.starts_with(DEFAULT_INPUT_PREFIX) || name.starts_with(DEFAULT_STATE_PREFIX) {
            let replacement = match input.get_type(ctx) {
                Type::BV(width) => ctx.zero(width),
                Type::Array(tpe) => ctx.zero_array(tpe),
            };
            replace_map.insert(input, replacement);
            false
        } else {
            true
        }
    });

    // replace any use of the input with zero
    do_transform(
        ctx,
        sys,
        ExprTransformMode::SingleStep,
        |_ctx, expr, _children| replace_map.get(&expr).cloned(),
        false,
    );
}

/// Applies simplifications to the expressions used in the system.
pub fn simplify_expressions(ctx: &mut Context, sys: &mut TransitionSystem) {
    do_transform(ctx, sys, ExprTransformMode::FixedPoint, simplify, false);
}

pub fn do_transform(
    ctx: &mut Context,
    sys: &mut TransitionSystem,
    mode: ExprTransformMode,
    tran: impl FnMut(&mut Context, ExprRef, &[ExprRef]) -> Option<ExprRef>,
    update_inputs_and_states: bool,
) {
    // update all expressions used in the transition system
    let todo = sys.get_all_exprs();
    let mut transformed = DenseExprMetaData::default();
    do_transform_expr(ctx, mode, &mut transformed, todo, tran);

    // update transition system signals to point to updated expressions
    sys.update_expressions(
        |old_expr| {
            if mode == ExprTransformMode::FixedPoint {
                get_fixed_point(&mut transformed, old_expr)
            } else {
                transformed[old_expr]
            }
        },
        update_inputs_and_states,
    );
}
