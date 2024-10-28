// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ir::*;
use baa::WidthInt;
use egg::Language;
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};

/// Intermediate expression language for bit vector arithmetic rewrites.
/// Inspired by: "ROVER: RTL Optimization via Verified E-Graph Rewriting" (TCAD'24)
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Arith {
    Symbol(StringRef, WidthInt),
    BinOp(
        [egg::Id; 2],
        BinOp,
        WidthInt,
        WidthInt,
        bool,
        WidthInt,
        bool,
    ),
}

impl Display for Arith {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Arith::Symbol(name, _) => write!(f, "{:?}", name),
            Arith::BinOp(_, op, wo, wa, sa, wb, sb) => write!(f, "{op} {wo} {wa} {sa} {wb} {sb}"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    LeftShift,
    RightShift,
    ArithmeticRightShift,
}

impl Display for BinOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mul => write!(f, "*"),
            BinOp::LeftShift => write!(f, "<<"),
            BinOp::RightShift => write!(f, ">>"),
            BinOp::ArithmeticRightShift => write!(f, ">>>"),
        }
    }
}

impl egg::Language for Arith {
    fn matches(&self, other: &Self) -> bool {
        // quick check to ensure that we are comparing the same kind of expression
        if std::mem::discriminant(self) != std::mem::discriminant(other) {
            return false;
        }
        // special comparisons for additional attributes
        match (self, other) {
            (Arith::Symbol(n0, w0), Arith::Symbol(n1, w1)) => n0 == n1 && w0 == w1,
            (
                Arith::BinOp(_, o0, wo_0, wa_0, sa_0, wb_0, sb_0),
                Arith::BinOp(_, o1, wo_1, wa_1, sa_1, wb_1, sb_1),
            ) => {
                o0 == o1
                    && wo_0 == wo_1
                    && wa_0 == wa_1
                    && wb_0 == wb_1
                    && sa_0 == sa_1
                    && sb_0 == sb_1
            }
            (_, _) => todo!("Compare {self:?} and {other:?}"),
        }
    }

    fn children(&self) -> &[egg::Id] {
        match self {
            Arith::BinOp(cc, ..) => cc,
            Arith::Symbol(_, _) => &[],
        }
    }

    fn children_mut(&mut self) -> &mut [egg::Id] {
        match self {
            Arith::BinOp(cc, ..) => cc,
            Arith::Symbol(_, _) => &mut [],
        }
    }
}

impl egg::FromOp for Arith {
    type Error = ();

    fn from_op(op: &str, _children: Vec<egg::Id>) -> Result<Self, Self::Error> {
        todo!("from_op({op})")
    }
}

/// Convert from our internal IR to the arithmetic expression IR suitable for rewrites.
pub fn to_arith(ctx: &Context, e: ExprRef) -> egg::RecExpr<Arith> {
    let mut out = egg::RecExpr::default();
    traversal::bottom_up_multi_pat(
        ctx,
        e,
        |ctx, expr, children| {
            // ignore any sing or zero extension when calculating the children
            expr.for_each_child(|c| {
                children.push(remove_ext(ctx, *c).0);
            });
        },
        |_ctx, expr, children| match *expr {
            Expr::BVSymbol { name, width } => out.add(Arith::Symbol(name, width)),
            Expr::BVAdd(a, b, width) => out.add(convert_bin_op(
                ctx,
                BinOp::Add,
                a,
                b,
                width,
                children[0],
                children[1],
            )),
            Expr::BVSub(a, b, width) => out.add(convert_bin_op(
                ctx,
                BinOp::Sub,
                a,
                b,
                width,
                children[0],
                children[1],
            )),
            Expr::BVMul(a, b, width) => out.add(convert_bin_op(
                ctx,
                BinOp::Mul,
                a,
                b,
                width,
                children[0],
                children[1],
            )),
            Expr::BVShiftLeft(a, b, width) => out.add(convert_bin_op(
                ctx,
                BinOp::LeftShift,
                a,
                b,
                width,
                children[0],
                children[1],
            )),
            Expr::BVShiftRight(a, b, width) => out.add(convert_bin_op(
                ctx,
                BinOp::RightShift,
                a,
                b,
                width,
                children[0],
                children[1],
            )),
            Expr::BVArithmeticShiftRight(a, b, width) => out.add(convert_bin_op(
                ctx,
                BinOp::ArithmeticRightShift,
                a,
                b,
                width,
                children[0],
                children[1],
            )),
            _ => todo!("{}", expr.serialize_to_str(ctx)),
        },
    );
    out
}

fn convert_bin_op(
    ctx: &Context,
    op: BinOp,
    a: ExprRef,
    b: ExprRef,
    width_out: WidthInt,
    converted_a: egg::Id,
    converted_b: egg::Id,
) -> Arith {
    // see the actual children (excluding any extensions) and determine sign
    let (base_a, sign_a) = remove_ext(ctx, a);
    let width_a = base_a.get_bv_type(ctx).unwrap();
    let (base_b, sign_b) = remove_ext(ctx, b);
    let width_b = base_b.get_bv_type(ctx).unwrap();
    debug_assert_eq!(width_out, a.get_bv_type(ctx).unwrap());
    debug_assert_eq!(width_out, b.get_bv_type(ctx).unwrap());
    Arith::BinOp(
        [converted_b, converted_a],
        op,
        width_out,
        width_a,
        sign_a,
        width_b,
        sign_b,
    )
}

/// Removes any sign or zero extend expressions and returns whether the removed extension was signed.
fn remove_ext(ctx: &Context, e: ExprRef) -> (ExprRef, bool) {
    match ctx.get(e) {
        Expr::BVZeroExt { e, .. } => (remove_ext(ctx, *e).0, false),
        Expr::BVSignExt { e, .. } => (remove_ext(ctx, *e).0, true),
        _ => (e, false),
    }
}

/// Convert from the arithmetic expression IR back to our internal SMTLib based IR.
pub fn from_arith(ctx: &mut Context, expr: &egg::RecExpr<Arith>) -> ExprRef {
    let expressions = expr.as_ref();
    let mut todo = vec![(expressions.len() - 1, false)];
    let mut stack = Vec::with_capacity(4);

    while let Some((e, bottom_up)) = todo.pop() {
        let expr = &expressions[e];

        // Check if there are children that we need to compute first.
        if !bottom_up && !expr.children().is_empty() {
            todo.push((e, true));
            for child_id in expr.children() {
                todo.push((usize::from(*child_id), false));
            }
            continue;
        }

        // Otherwise, all arguments are available on the stack for us to use.
        let result = match expr {
            Arith::Symbol(name, width) => ctx.symbol(*name, Type::BV(*width)),
            Arith::BinOp(_, op, wo, wa, sa, wb, sb) => {
                let a = extend(ctx, stack.pop().unwrap(), *wo, *wa, *sa);
                let b = extend(ctx, stack.pop().unwrap(), *wo, *wb, *sb);
                match op {
                    BinOp::Add => ctx.add(a, b),
                    BinOp::Sub => ctx.sub(a, b),
                    BinOp::Mul => ctx.mul(a, b),
                    BinOp::LeftShift => ctx.shift_left(a, b),
                    BinOp::RightShift => ctx.shift_right(a, b),
                    BinOp::ArithmeticRightShift => ctx.arithmetic_shift_right(a, b),
                }
            }
        };
        stack.push(result);
    }

    debug_assert_eq!(stack.len(), 1);
    stack.pop().unwrap()
}

fn extend(
    ctx: &mut Context,
    expr: ExprRef,
    w_out: WidthInt,
    w_in: WidthInt,
    signed: bool,
) -> ExprRef {
    debug_assert_eq!(expr.get_bv_type(ctx).unwrap(), w_in);
    match w_out.cmp(&w_in) {
        Ordering::Less => unreachable!("cannot extend from {w_in} to {w_out}"),
        Ordering::Equal => expr,
        Ordering::Greater if !signed => ctx.zero_extend(expr, w_out - w_in),
        Ordering::Greater => ctx.sign_extend(expr, w_out - w_in),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_data_path_verification_fig_1() {
        let mut ctx = Context::default();
        let a = ctx.bv_symbol("A", 16);
        let b = ctx.bv_symbol("B", 16);
        let m = ctx.bv_symbol("M", 4);
        let n = ctx.bv_symbol("N", 4);
        let spec = ctx.build(|c| {
            c.mul(
                c.zero_extend(c.shift_left(c.zero_extend(a, 15), c.zero_extend(m, 27)), 32),
                c.zero_extend(c.shift_left(c.zero_extend(b, 15), c.zero_extend(n, 27)), 32),
            )
        });
        let implementation = ctx.build(|c| {
            c.shift_left(
                c.zero_extend(c.mul(c.zero_extend(a, 16), c.zero_extend(b, 16)), 31),
                c.zero_extend(c.add(c.zero_extend(m, 1), c.zero_extend(n, 1)), 58),
            )
        });

        let spec_e = to_arith(&ctx, spec);
        let impl_e = to_arith(&ctx, implementation);

        // convert back into out IR
        let spec_back = from_arith(&mut ctx, &spec_e);
        let impl_back = from_arith(&mut ctx, &impl_e);

        // because of hash consing, we should get the exact same expr ref back
        assert_eq!(spec_back, spec);
        assert_eq!(impl_back, implementation);
    }
}
