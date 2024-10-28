// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ir::*;
use baa::WidthInt;
use egg::Language;
use std::cmp::Ordering;

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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    LeftShift,
    RightShift,
    ArithmeticRightShift,
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

    fn from_op(op: &str, children: Vec<egg::Id>) -> Result<Self, Self::Error> {
        todo!("from_op({op})")
    }
}

/// Convert from our internal IR to the arithmetic expression IR suitable for rewrites.
pub fn to_arith(ctx: &Context, e: ExprRef) -> egg::RecExpr<Arith> {
    let mut out = egg::RecExpr::default();
    traversal::bottom_up(ctx, e, |_ctx, expr, children| match *expr {
        Expr::BVSymbol { name, width } => out.add(Arith::Symbol(name, width)),
        Expr::BVMul(a, b, width) => todo!(),
        _ => todo!(),
    });
    out
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
