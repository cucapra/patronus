// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::expr::meta::get_fixed_point;
use crate::expr::*;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ExprTransformMode {
    SingleStep,
    FixedPoint,
}

/// transform an expression with a single step (no fixed point) and no persistent cache
#[inline]
pub fn simple_transform_expr(
    ctx: &mut Context,
    e: ExprRef,
    tran: impl FnMut(&mut Context, ExprRef, &[ExprRef]) -> Option<ExprRef>,
) -> ExprRef {
    let mut cache = SparseExprMap::default();
    do_transform_expr(
        ctx,
        ExprTransformMode::SingleStep,
        &mut cache,
        vec![e],
        tran,
    );
    cache[e].unwrap()
}

#[inline]
pub fn do_transform_expr<T: ExprMap<Option<ExprRef>>>(
    ctx: &mut Context,
    mode: ExprTransformMode,
    transformed: &mut T,
    mut todo: Vec<ExprRef>,
    mut tran: impl FnMut(&mut Context, ExprRef, &[ExprRef]) -> Option<ExprRef>,
) {
    let mut children = Vec::with_capacity(4);

    while let Some(expr_ref) = todo.pop() {
        // check to see if we translated all the children
        children.clear();
        let mut children_changed = false; // track whether any of the children changed
        let mut all_transformed = true; // tracks whether all children have been transformed or if there is more work to do
        ctx[expr_ref].for_each_child(|c| {
            let transformed_child = if mode == ExprTransformMode::FixedPoint {
                get_fixed_point(transformed, *c)
            } else {
                transformed[*c]
            };
            match transformed_child {
                Some(new_child_expr) => {
                    if new_child_expr != *c {
                        children_changed = true; // child changed
                    }
                    children.push(new_child_expr);
                }
                None => {
                    if all_transformed {
                        todo.push(expr_ref);
                    }
                    all_transformed = false;
                    todo.push(*c);
                }
            }
        });
        if !all_transformed {
            continue;
        }

        // call out to the transform
        let tran_res = tran(ctx, expr_ref, &children);
        let new_expr_ref = match tran_res {
            Some(e) => e,
            None => {
                if children_changed {
                    update_expr_children(ctx, expr_ref, &children)
                } else {
                    // if no children changed and the transform does not want to do changes,
                    // we can just keep the old expression
                    expr_ref
                }
            }
        };
        // remember the transformed version
        transformed[expr_ref] = Some(new_expr_ref);

        // in fixed point mode, we might not be done yet
        let is_at_fixed_point = expr_ref == new_expr_ref;
        if mode == ExprTransformMode::FixedPoint
            && !is_at_fixed_point
            && transformed[new_expr_ref].is_none()
        {
            // see if we can further simplify the new expression
            todo.push(new_expr_ref);
        }
    }
}

fn update_expr_children(ctx: &mut Context, expr_ref: ExprRef, children: &[ExprRef]) -> ExprRef {
    let new_expr = match (&ctx[expr_ref], children) {
        (Expr::BVSymbol { .. }, _) => panic!("No children, should never get here."),
        (Expr::BVLiteral { .. }, _) => panic!("No children, should never get here."),
        (Expr::BVZeroExt { by, width, .. }, [e]) => Expr::BVZeroExt {
            e: *e,
            by: *by,
            width: *width,
        },
        (Expr::BVSignExt { by, width, .. }, [e]) => Expr::BVSignExt {
            e: *e,
            by: *by,
            width: *width,
        },
        (Expr::BVSlice { hi, lo, .. }, [e]) => Expr::BVSlice {
            e: *e,
            hi: *hi,
            lo: *lo,
        },
        (Expr::BVNot(_, width), [e]) => Expr::BVNot(*e, *width),
        (Expr::BVNegate(_, width), [e]) => Expr::BVNegate(*e, *width),
        (Expr::BVEqual(_, _), [a, b]) => Expr::BVEqual(*a, *b),
        (Expr::BVImplies(_, _), [a, b]) => Expr::BVImplies(*a, *b),
        (Expr::BVGreater(_, _), [a, b]) => Expr::BVGreater(*a, *b),
        (Expr::BVGreaterSigned(_, _, w), [a, b]) => Expr::BVGreaterSigned(*a, *b, *w),
        (Expr::BVGreaterEqual(_, _), [a, b]) => Expr::BVGreaterEqual(*a, *b),
        (Expr::BVGreaterEqualSigned(_, _, w), [a, b]) => Expr::BVGreaterEqualSigned(*a, *b, *w),
        (Expr::BVConcat(_, _, w), [a, b]) => Expr::BVConcat(*a, *b, *w),
        (Expr::BVAnd(_, _, w), [a, b]) => Expr::BVAnd(*a, *b, *w),
        (Expr::BVOr(_, _, w), [a, b]) => Expr::BVOr(*a, *b, *w),
        (Expr::BVXor(_, _, w), [a, b]) => Expr::BVXor(*a, *b, *w),
        (Expr::BVShiftLeft(_, _, w), [a, b]) => Expr::BVShiftLeft(*a, *b, *w),
        (Expr::BVArithmeticShiftRight(_, _, w), [a, b]) => Expr::BVArithmeticShiftRight(*a, *b, *w),
        (Expr::BVShiftRight(_, _, w), [a, b]) => Expr::BVShiftRight(*a, *b, *w),
        (Expr::BVAdd(_, _, w), [a, b]) => Expr::BVAdd(*a, *b, *w),
        (Expr::BVMul(_, _, w), [a, b]) => Expr::BVMul(*a, *b, *w),
        (Expr::BVSignedDiv(_, _, w), [a, b]) => Expr::BVSignedDiv(*a, *b, *w),
        (Expr::BVUnsignedDiv(_, _, w), [a, b]) => Expr::BVUnsignedDiv(*a, *b, *w),
        (Expr::BVSignedMod(_, _, w), [a, b]) => Expr::BVSignedMod(*a, *b, *w),
        (Expr::BVSignedRem(_, _, w), [a, b]) => Expr::BVSignedRem(*a, *b, *w),
        (Expr::BVUnsignedRem(_, _, w), [a, b]) => Expr::BVUnsignedRem(*a, *b, *w),
        (Expr::BVSub(_, _, w), [a, b]) => Expr::BVSub(*a, *b, *w),
        (Expr::BVArrayRead { width, .. }, [array, index]) => Expr::BVArrayRead {
            array: *array,
            index: *index,
            width: *width,
        },
        (Expr::BVIte { .. }, [cond, tru, fals]) => Expr::BVIte {
            cond: *cond,
            tru: *tru,
            fals: *fals,
        },
        (Expr::ArraySymbol { .. }, _) => panic!("No children, should never get here."),
        (
            Expr::ArrayConstant {
                index_width,
                data_width,
                ..
            },
            [e],
        ) => Expr::ArrayConstant {
            e: *e,
            index_width: *index_width,
            data_width: *data_width,
        },
        (Expr::ArrayEqual(_, _), [a, b]) => Expr::ArrayEqual(*a, *b),
        (Expr::ArrayStore { .. }, [array, index, data]) => Expr::ArrayStore {
            array: *array,
            index: *index,
            data: *data,
        },
        (Expr::ArrayIte { .. }, [cond, tru, fals]) => Expr::ArrayIte {
            cond: *cond,
            tru: *tru,
            fals: *fals,
        },
        (other, _) => {
            todo!("implement code to re-create expression `{other:?}` with updated children")
        }
    };
    ctx.add_expr(new_expr)
}
