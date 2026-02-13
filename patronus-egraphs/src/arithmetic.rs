// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::BitVecOps;
use egg::{Analysis, DidMerge, Id, Language, RecExpr, define_language};
use patronus::expr::*;
use std::cmp::{Ordering, max};
use std::fmt::{Display, Formatter};
use std::str::FromStr;

define_language! {
    /// Intermediate expression language for bit vector arithmetic rewrites.
    /// Inspired by: "ROVER: RTL Optimization via Verified E-Graph Rewriting" (TCAD'24)
    /// arguments for binop: w, w_a, s_a, a, w_b, s_b, b
    pub enum Arith {
        // operations on actual bit-vec values
        "+" = Add([Id; 7]),
        "-" = Sub([Id; 7]),
        "*" = Mul([Id; 7]),
        "<<" = LeftShift([Id; 7]),
        ">>" = RightShift([Id; 7]),
        ">>>" = ArithmeticRightShift([Id; 7]),
        // operations on widths
        "max+1" = WidthMaxPlus1([Id; 2]),
        "wlsh" = WidthLeftShift([Id; 2]),
        Width(WidthValue),
        Sign(Sign),
        // not a width, but a value constant
        Const(u64),
        Symbol(String),
    }
}

/// Wrapper struct in order to do custom parsing.
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct WidthValue(WidthInt);

pub(crate) fn eval_width_max_plus_1(wa: WidthInt, wb: WidthInt) -> WidthInt {
    max(wa, wb) + 1
}

pub(crate) fn eval_width_left_shift(wa: WidthInt, wb: WidthInt) -> WidthInt {
    if wb >= WidthInt::BITS {
        // very very very large width, not what you want
        WidthInt::MAX
    } else {
        let max_shift: WidthInt = (1 << wb) - 1;
        wa + max_shift
    }
}

// this allows us to use ArithWidthConst as an argument to ctx.bit_vec_val
impl From<WidthValue> for u128 {
    fn from(value: WidthValue) -> Self {
        value.0 as u128
    }
}

impl From<WidthValue> for WidthInt {
    fn from(value: WidthValue) -> Self {
        value.0
    }
}

impl From<WidthInt> for Arith {
    fn from(value: WidthInt) -> Self {
        Arith::Width(WidthValue(value))
    }
}

impl FromStr for WidthValue {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some(suffix) = s.strip_prefix("W<") {
            if let Some(value) = suffix.strip_suffix(">") {
                match value.parse() {
                    Err(_) => Err(()),
                    Ok(w) => Ok(Self(w)),
                }
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    }
}

impl Display for WidthValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "W<{}>", self.0)
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub enum Sign {
    Signed,
    Unsigned,
}

// this allows us to use Sign as an argument to ctx.bit_vec_val
impl From<Sign> for u128 {
    fn from(value: Sign) -> Self {
        let w: WidthInt = value.into();
        w as u128
    }
}

impl From<Sign> for WidthInt {
    fn from(value: Sign) -> Self {
        match value {
            Sign::Signed => 1,
            Sign::Unsigned => 0,
        }
    }
}

impl From<Sign> for Arith {
    fn from(value: Sign) -> Self {
        Arith::Sign(value)
    }
}

impl FromStr for Sign {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "sign" => Ok(Self::Signed),
            "unsign" => Ok(Self::Unsigned),
            _ => Err(()),
        }
    }
}

impl Display for Sign {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Sign::Signed => write!(f, "sign"),
            Sign::Unsigned => write!(f, "unsign"),
        }
    }
}

/// Ensures that derived width constants on the rhs of our rules are correctly
/// simplified and unioned with their constant version.
#[derive(Default)]
pub struct WidthConstantFold;

impl Analysis<Arith> for WidthConstantFold {
    type Data = Option<WidthInt>;

    fn make(egraph: &egg::EGraph<Arith, Self>, expr: &Arith) -> Self::Data {
        let x = |i: &Id| egraph[*i].data;
        match expr {
            &Arith::Width(w) => Some(w.0),
            Arith::WidthMaxPlus1([a, b]) => Some(eval_width_max_plus_1(x(a)?, x(b)?)),
            Arith::WidthLeftShift([a, b]) => Some(eval_width_left_shift(x(a)?, x(b)?)),
            _ => None,
        }
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        egg::merge_max(to, from)
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some(w) = egraph[id].data {
            let added = egraph.add(Arith::Width(WidthValue(w)));
            egraph.union(id, added);
        }
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
        |_ctx, expr, children| match ctx[expr].clone() {
            Expr::BVSymbol { name, .. } => out.add(Arith::Symbol(ctx[name].to_string())),
            Expr::BVAdd(a, b, width) => convert_bin_op(
                ctx,
                &mut out,
                Arith::Add,
                a,
                b,
                width,
                children[0],
                children[1],
            ),
            Expr::BVSub(a, b, width) => convert_bin_op(
                ctx,
                &mut out,
                Arith::Sub,
                a,
                b,
                width,
                children[0],
                children[1],
            ),
            Expr::BVMul(a, b, width) => convert_bin_op(
                ctx,
                &mut out,
                Arith::Mul,
                a,
                b,
                width,
                children[0],
                children[1],
            ),
            Expr::BVShiftLeft(a, b, width) => convert_bin_op(
                ctx,
                &mut out,
                Arith::LeftShift,
                a,
                b,
                width,
                children[0],
                children[1],
            ),
            Expr::BVShiftRight(a, b, width) => convert_bin_op(
                ctx,
                &mut out,
                Arith::RightShift,
                a,
                b,
                width,
                children[0],
                children[1],
            ),
            Expr::BVArithmeticShiftRight(a, b, width) => convert_bin_op(
                ctx,
                &mut out,
                Arith::ArithmeticRightShift,
                a,
                b,
                width,
                children[0],
                children[1],
            ),
            _ => todo!("{}", expr.serialize_to_str(ctx)),
        },
    );
    out
}

#[allow(clippy::too_many_arguments)]
fn convert_bin_op(
    ctx: &Context,
    out: &mut RecExpr<Arith>,
    op: fn([Id; 7]) -> Arith,
    a: ExprRef,
    b: ExprRef,
    width_out: WidthInt,
    converted_a: Id,
    converted_b: Id,
) -> Id {
    // see the actual children (excluding any extensions) and determine sign
    let (base_a, sign_a) = remove_ext(ctx, a);
    let width_a = base_a.get_bv_type(ctx).unwrap();
    let (base_b, sign_b) = remove_ext(ctx, b);
    let width_b = base_b.get_bv_type(ctx).unwrap();
    debug_assert_eq!(width_out, a.get_bv_type(ctx).unwrap());
    debug_assert_eq!(width_out, b.get_bv_type(ctx).unwrap());
    // convert signedness and widths into e-nodes
    let width_out = out.add(width_out.into());
    let width_a = out.add(width_a.into());
    let width_b = out.add(width_b.into());
    let sign_a = out.add(sign_a.into());
    let sign_b = out.add(sign_b.into());
    out.add(op([
        width_out,
        width_a,
        sign_a,
        converted_a,
        width_b,
        sign_b,
        converted_b,
    ]))
}

/// Removes any sign or zero extend expressions and returns whether the removed extension was signed.
fn remove_ext(ctx: &Context, e: ExprRef) -> (ExprRef, Sign) {
    match ctx[e] {
        Expr::BVZeroExt { e, .. } => (remove_ext(ctx, e).0, Sign::Unsigned),
        Expr::BVSignExt { e, .. } => (remove_ext(ctx, e).0, Sign::Signed),
        _ => (e, Sign::Unsigned),
    }
}

/// Convert from the arithmetic expression IR back to our internal SMTLib based IR.
pub fn from_arith(ctx: &mut Context, expr: &RecExpr<Arith>) -> ExprRef {
    let expressions = expr.as_ref();
    let mut todo = vec![(expressions.len() - 1, false, 0)];
    let mut stack = Vec::with_capacity(4);
    let mut child_widths = Vec::with_capacity(8);

    while let Some((e, bottom_up, expected_width)) = todo.pop() {
        let expr = &expressions[e];

        // Check if there are children that we need to compute first.
        if !bottom_up && !expr.children().is_empty() {
            todo.push((e, true, expected_width));
            get_child_widths(e, expressions, &mut child_widths);
            for (child_id, expected_w) in expr.children().iter().zip(child_widths.iter()) {
                todo.push((usize::from(*child_id), false, *expected_w));
            }
            child_widths.clear();
            continue;
        }

        // Otherwise, all arguments are available on the stack for us to use.
        let result = match expr {
            Arith::Symbol(name) => {
                debug_assert!(expected_width > 0, "unknown width for symbol `{name}`!");
                ctx.bv_symbol(name, expected_width)
            }
            Arith::Add(_) => patronus_bin_op(ctx, &mut stack, |ctx, a, b| ctx.add(a, b)),
            Arith::Sub(_) => patronus_bin_op(ctx, &mut stack, |ctx, a, b| ctx.sub(a, b)),
            Arith::Mul(_) => patronus_bin_op(ctx, &mut stack, |ctx, a, b| ctx.mul(a, b)),
            Arith::LeftShift(_) => {
                patronus_bin_op(ctx, &mut stack, |ctx, a, b| ctx.shift_left(a, b))
            }
            Arith::RightShift(_) => {
                patronus_bin_op(ctx, &mut stack, |ctx, a, b| ctx.shift_right(a, b))
            }
            Arith::ArithmeticRightShift(_) => patronus_bin_op(ctx, &mut stack, |ctx, a, b| {
                ctx.arithmetic_shift_right(a, b)
            }),
            Arith::WidthMaxPlus1(_) => {
                let a = get_u64(ctx, stack.pop().unwrap()) as WidthInt;
                let b = get_u64(ctx, stack.pop().unwrap()) as WidthInt;
                ctx.bit_vec_val(eval_width_max_plus_1(a, b), 32)
            }
            Arith::WidthLeftShift(_) => {
                let a = get_u64(ctx, stack.pop().unwrap()) as WidthInt;
                let b = get_u64(ctx, stack.pop().unwrap()) as WidthInt;
                ctx.bit_vec_val(eval_width_left_shift(a, b), 32)
            }
            Arith::Width(width) => ctx.bit_vec_val(*width, 32),
            Arith::Sign(sign) => ctx.bit_vec_val(*sign, 1),
            Arith::Const(value) => {
                debug_assert!(expected_width > 0, "unknown width for constant `{value}`!");
                // patronus will normally throw an error, if the value does not fit into the width
                // however, in our case, we want to just ignore the bits that get lost
                let value = if expected_width < u64::BITS {
                    *value & ((1u64 << expected_width) - 1)
                } else {
                    *value
                };
                ctx.bit_vec_val(value, expected_width)
            }
        };
        stack.push(result);
    }

    debug_assert_eq!(stack.len(), 1);
    stack.pop().unwrap()
}

/// extracts the expected widths of all proper child expressions
fn get_child_widths(root: usize, expressions: &[Arith], out: &mut Vec<WidthInt>) {
    debug_assert!(out.is_empty());
    let expr = &expressions[root];
    if is_bin_op(expr) {
        // w, w_a, s_a, a, w_b, s_b, b
        let a_width = get_width(usize::from(expr.children()[1]), expressions);
        let b_width = get_width(usize::from(expr.children()[4]), expressions);
        // we set don't cares to zero
        out.extend_from_slice(&[0, 0, 0, a_width, 0, 0, b_width]);
    } else {
        match expr {
            // calculated width
            Arith::WidthMaxPlus1(_) | Arith::WidthLeftShift(_) => {
                // widths are always propagated as 32-bit values
                out.extend_from_slice(&[32, 32]);
            }
            _ => {
                // otherwise there is nothing to do
                debug_assert!(expr.children().is_empty(), "{expr:?}")
            }
        }
    }
}

fn get_width(root: usize, expressions: &[Arith]) -> WidthInt {
    match &expressions[root] {
        Arith::Width(w) => w.0,
        Arith::WidthMaxPlus1([a, b]) => {
            let a = get_width(usize::from(*a), expressions);
            let b = get_width(usize::from(*b), expressions);
            eval_width_max_plus_1(a, b)
        }
        Arith::WidthLeftShift([a, b]) => {
            let a = get_width(usize::from(*a), expressions);
            let b = get_width(usize::from(*b), expressions);
            eval_width_left_shift(a, b)
        }
        other => todo!("calculate width for {other:?}"),
    }
}

pub fn is_bin_op(a: &Arith) -> bool {
    matches!(
        a,
        Arith::Add(_)
            | Arith::Sub(_)
            | Arith::Mul(_)
            | Arith::LeftShift(_)
            | Arith::RightShift(_)
            | Arith::ArithmeticRightShift(_)
    )
}

fn patronus_bin_op(
    ctx: &mut Context,
    stack: &mut Vec<ExprRef>,
    op: fn(&mut Context, ExprRef, ExprRef) -> ExprRef,
) -> ExprRef {
    // get parameters from stack
    let wo = get_u64(ctx, stack.pop().unwrap()) as WidthInt;
    let wa = get_u64(ctx, stack.pop().unwrap()) as WidthInt;
    let sa = get_u64(ctx, stack.pop().unwrap()) != 0;
    let a = stack.pop().unwrap();
    let wb = get_u64(ctx, stack.pop().unwrap()) as WidthInt;
    let sb = get_u64(ctx, stack.pop().unwrap()) != 0;
    let b = stack.pop().unwrap();

    // slice and extend appropriately
    let arg_max_width = max(wa, wb);
    let calc_width = max(arg_max_width, wo);
    let a = extend(ctx, a, calc_width, wa, sa);
    let b = extend(ctx, b, calc_width, wb, sb);
    let res = op(ctx, a, b);
    if calc_width == wo {
        res
    } else {
        debug_assert!(calc_width > wo);
        ctx.slice(res, wo - 1, 0)
    }
}

fn get_u64(ctx: &Context, e: ExprRef) -> u64 {
    match &ctx[e] {
        Expr::BVLiteral(value) => value.get(ctx).to_u64().unwrap(),
        other => unreachable!(
            "{} is not a bit vector literal!",
            other.serialize_to_str(ctx)
        ),
    }
}

fn extend(
    ctx: &mut Context,
    expr: ExprRef,
    w_out: WidthInt,
    w_in: WidthInt,
    signed: bool,
) -> ExprRef {
    debug_assert_eq!(
        expr.get_bv_type(ctx).unwrap(),
        w_in,
        "{}",
        expr.serialize_to_str(ctx)
    );
    match w_out.cmp(&w_in) {
        Ordering::Less => unreachable!("cannot extend from {w_in} to {w_out}"),
        Ordering::Equal => expr,
        Ordering::Greater if !signed => ctx.zero_extend(expr, w_out - w_in),
        Ordering::Greater => ctx.sign_extend(expr, w_out - w_in),
    }
}

pub type EGraph = egg::EGraph<Arith, WidthConstantFold>;

/// Finds a width or sign constant in the e-class referred to by the substitution
/// and returns its value. Errors if no such constant can be found.
pub fn get_const_width_or_sign(egraph: &EGraph, id: Id) -> Option<WidthInt> {
    egraph[id]
        .nodes
        .iter()
        .flat_map(|n| match n {
            Arith::Width(w) => Some((*w).into()),
            Arith::Sign(s) => Some((*s).into()),
            _ => None,
        })
        .next()
}

#[cfg(test)]
pub(crate) fn verification_fig_1(ctx: &mut Context) -> (ExprRef, ExprRef) {
    let a = ctx.bv_symbol("A", 16);
    let b = ctx.bv_symbol("B", 16);
    let m = ctx.bv_symbol("M", 4);
    let n = ctx.bv_symbol("N", 4);
    // (A << M) * (B << N)
    let spec = ctx.build(|c| {
        c.mul(
            c.zero_extend(c.shift_left(c.zero_extend(a, 15), c.zero_extend(m, 27)), 32),
            c.zero_extend(c.shift_left(c.zero_extend(b, 15), c.zero_extend(n, 27)), 32),
        )
    });
    // (A * B) << (M + N)
    let implementation = ctx.build(|c| {
        c.shift_left(
            c.zero_extend(c.mul(c.zero_extend(a, 16), c.zero_extend(b, 16)), 31),
            c.zero_extend(c.add(c.zero_extend(m, 1), c.zero_extend(n, 1)), 58),
        )
    });
    (spec, implementation)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_data_path_verification_fig_1_conversion() {
        let mut ctx = Context::default();
        let (spec, implementation) = verification_fig_1(&mut ctx);

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
