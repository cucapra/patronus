// Copyright 2023 The Regents of the University of California
// Copyright 2024-2026 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use super::{
    BVLitValue, Context, Expr, ExprMap, ExprRef, SerializableIrNode, SparseExprMap, TypeCheck,
    WidthInt, do_transform_expr, find_symbols,
};
use crate::expr::meta::get_fixed_point;
use crate::expr::transform::ExprTransformMode;
use crate::smt::{CheckSatResponse, SolverContext};
use baa::BitVecOps;
use smallvec::{SmallVec, smallvec};

/// Applies simplifications to a single expression.
pub fn simplify_single_expression(ctx: &mut Context, expr: ExprRef) -> ExprRef {
    let mut simplifier = Simplifier::new(SparseExprMap::default());
    simplifier.simplify(ctx, expr)
}

/// Performs simplification and canonicalization on expressions and caches the results.
pub struct Simplifier<T: ExprMap<Option<ExprRef>>> {
    cache: T,
}

impl<T: ExprMap<Option<ExprRef>>> Simplifier<T> {
    pub fn new(cache: T) -> Self {
        Self { cache }
    }

    pub fn simplify(&mut self, ctx: &mut Context, e: ExprRef) -> ExprRef {
        do_transform_expr(
            ctx,
            ExprTransformMode::FixedPoint,
            &mut self.cache,
            vec![e],
            simplify,
        );
        get_fixed_point(&mut self.cache, e).unwrap()
    }

    /// Uses an SMT solver to check all simplification steps that have been made with this Simplifier.
    /// Returns the number of incorrect simplifications.
    pub fn verify_simplification(
        &self,
        ctx: &mut Context,
        solver: &mut impl SolverContext,
    ) -> crate::smt::Result<usize> {
        let mut incorrect = 0;
        let mut correct = 0;
        for (key, &value) in self.cache.iter() {
            if let Some(simplified) = value {
                let key_symbols = find_symbols(ctx, key);
                let simpl_symbols = find_symbols(ctx, simplified);
                let symbols: Vec<_> = key_symbols.union(&simpl_symbols).cloned().collect();
                solver.push()?;
                for &sym in symbols.iter() {
                    solver.declare_const(ctx, sym)?;
                }
                let not_eq = ctx.distinct(key, simplified);
                solver.assert(ctx, not_eq)?;
                match solver.check_sat()? {
                    CheckSatResponse::Sat => {
                        let key_value = solver.get_value(ctx, key)?;
                        let simplified_value = solver.get_value(ctx, simplified)?;
                        println!(
                            "{} ({}) =/= ({}) {}",
                            key.serialize_to_str(ctx),
                            key_value.serialize_to_str(ctx),
                            simplified_value.serialize_to_str(ctx),
                            simplified.serialize_to_str(ctx)
                        );
                        let mut syms = vec![];
                        for &sym in symbols.iter() {
                            let value = solver.get_value(ctx, sym)?;
                            syms.push(format!(
                                "{}={}",
                                sym.serialize_to_str(ctx),
                                value.serialize_to_str(ctx)
                            ));
                        }
                        println!(" w/ {}", syms.join(", "));
                        incorrect += 1;
                    }
                    CheckSatResponse::Unsat => {
                        correct += 1;
                    } // OK
                    CheckSatResponse::Unknown => {} // OK
                }

                solver.pop()?;
            }
        }
        if incorrect > 0 {
            println!(
                "{incorrect} / {} simplifications were incorrect. See log.",
                incorrect + correct
            );
        }

        Ok(incorrect)
    }
}

/// Simplifies one expression (not its children)
pub(crate) fn simplify(ctx: &mut Context, expr: ExprRef, children: &[ExprRef]) -> Option<ExprRef> {
    match (ctx[expr].clone(), children) {
        (Expr::BVNot(_, _), [e]) => simplify_bv_not(ctx, *e),
        (Expr::BVZeroExt { by, .. }, [e]) => simplify_bv_zero_ext(ctx, *e, by),
        (Expr::BVSlice { lo, hi, .. }, [e]) => simplify_bv_slice(ctx, *e, hi, lo),
        (Expr::BVIte { .. }, [cond, tru, fals]) => simplify_ite(ctx, *cond, *tru, *fals),
        (Expr::BVConcat(..), [a, b]) => simplify_bv_concat(ctx, *a, *b),
        (Expr::BVEqual(..), [a, b]) => simplify_bv_equal(ctx, *a, *b),
        (Expr::BVAnd(..), [a, b]) => simplify_bv_and(ctx, *a, *b),
        (Expr::BVOr(..), [a, b]) => simplify_bv_or(ctx, *a, *b),
        (Expr::BVXor(..), [a, b]) => simplify_bv_xor(ctx, *a, *b),
        (Expr::BVImplies(..), [a, b]) => simplify_bv_implies(ctx, *a, *b),
        (Expr::BVGreaterEqual(..), [a, b]) => simplify_bv_greater_equal(ctx, *a, *b),
        (Expr::BVAdd(..), [a, b]) => simplify_bv_add(ctx, *a, *b),
        (Expr::BVMul(..), [a, b]) => simplify_bv_mul(ctx, *a, *b),
        (Expr::BVShiftLeft(_, _, w), [a, b]) => simplify_bv_shift_left(ctx, *a, *b, w),
        (Expr::BVShiftRight(_, _, w), [a, b]) => simplify_bv_shift_right(ctx, *a, *b, w),
        (Expr::BVSignExt { by, .. }, [e]) => simplify_bv_sign_ext(ctx, *e, by),
        (Expr::BVArithmeticShiftRight(_, _, w), [a, b]) => {
            simplify_bv_arithmetic_shift_right(ctx, *a, *b, w)
        }
        _ => None,
    }
}

fn simplify_ite(ctx: &mut Context, cond: ExprRef, tru: ExprRef, fals: ExprRef) -> Option<ExprRef> {
    // ite(_, a, a) -> a
    if tru == fals {
        return Some(tru);
    }

    // constant condition
    if let Expr::BVLiteral(value) = ctx[cond] {
        if value.get(ctx).is_false() {
            // ite(false, a, b) -> b
            return Some(fals);
        } else {
            // ite(true,  a, b) -> a
            return Some(tru);
        }
    }

    // boolean return type
    let value_width = ctx[tru].get_bv_type(ctx).unwrap();
    debug_assert_eq!(ctx[fals].get_bv_type(ctx), ctx[tru].get_bv_type(ctx));
    if value_width == 1 {
        // boolean value simplifications
        match (&ctx[tru], &ctx[fals]) {
            (Expr::BVLiteral(vt), Expr::BVLiteral(vf)) => {
                let res = match (
                    vt.get(ctx).to_bool().unwrap(),
                    vf.get(ctx).to_bool().unwrap(),
                ) {
                    // ite(cond, true, false) -> cond
                    (true, false) => cond,
                    // ite(cond, false, true) -> !cond
                    (false, true) => ctx.not(cond),
                    _ => unreachable!(
                        "both arguments are the same, this should have been handled earlier"
                    ),
                };
                Some(res)
            }
            (Expr::BVLiteral(vt), _) => {
                match vt.get(ctx).to_bool().unwrap() {
                    // ite(c, true, b) -> c | b
                    true => Some(ctx.or(cond, fals)),
                    // ite(c, false, b) -> !c & b
                    false => Some(ctx.build(|c| c.and(c.not(cond), fals))),
                }
            }
            (_, Expr::BVLiteral(vf)) => {
                match vf.get(ctx).to_bool().unwrap() {
                    // ite(c, a, true) -> !c | a
                    true => Some(ctx.build(|c| c.or(c.not(cond), tru))),
                    // ite(c, a, false) -> c & a
                    false => Some(ctx.and(cond, tru)),
                }
            }
            _ => None,
        }
    } else {
        None
    }
}

enum Lits {
    Two(BVLitValue, BVLitValue),
    One((BVLitValue, ExprRef), ExprRef),
    None,
}

/// Finds the maximum number of literals. Only works on commutative operations.
#[inline]
fn find_lits_commutative(ctx: &Context, a: ExprRef, b: ExprRef) -> Lits {
    match (&ctx[a], &ctx[b]) {
        (Expr::BVLiteral(va), Expr::BVLiteral(vb)) => Lits::Two(*va, *vb),
        (Expr::BVLiteral(va), _) => Lits::One((*va, a), b),
        (_, Expr::BVLiteral(vb)) => Lits::One((*vb, b), a),
        (_, _) => Lits::None,
    }
}

#[inline]
fn find_one_concat(ctx: &Context, a: ExprRef, b: ExprRef) -> Option<(ExprRef, ExprRef, ExprRef)> {
    match (&ctx[a], &ctx[b]) {
        (Expr::BVConcat(c_a, c_b, _), _) => Some((*c_a, *c_b, b)),
        (_, Expr::BVConcat(c_a, c_b, _)) => Some((*c_a, *c_b, a)),
        _ => None,
    }
}

fn simplify_bv_equal(ctx: &mut Context, a: ExprRef, b: ExprRef) -> Option<ExprRef> {
    // a == a -> true
    if a == b {
        return Some(ctx.get_true());
    }

    match find_lits_commutative(ctx, a, b) {
        Lits::Two(va, vb) => {
            // two values that are the same should always be hash-consed to the same ExprRef
            debug_assert!(!va.get(ctx).is_equal(&vb.get(ctx)));
            return Some(ctx.get_false());
        }
        Lits::One((lit, _), expr) => {
            if lit.is_true() {
                // a == true -> a
                return Some(expr);
            } else if lit.is_false() {
                // a == false -> !a
                return Some(ctx.not(expr));
            }
        }
        Lits::None => {}
    }

    // check to see if we are comparing to a concat
    if let Some((concat_a, concat_b, other)) = find_one_concat(ctx, a, b) {
        let a_width = ctx[concat_a].get_bv_type(ctx).unwrap();
        let b_width = ctx[concat_b].get_bv_type(ctx).unwrap();
        let width = a_width + b_width;
        debug_assert_eq!(width, other.get_bv_type(ctx).unwrap());
        let eq_a = ctx.build(|c| c.equal(concat_a, c.slice(other, width - 1, width - a_width)));
        let eq_b = ctx.build(|c| c.equal(concat_b, c.slice(other, b_width - 1, 0)));
        return Some(ctx.and(eq_a, eq_b));
    }

    None
}

fn simplify_bv_and(ctx: &mut Context, a: ExprRef, b: ExprRef) -> Option<ExprRef> {
    // a & a -> a
    if a == b {
        return Some(a);
    }

    // other simplifications depend on whether one or two of the values are a constant
    match find_lits_commutative(ctx, a, b) {
        Lits::Two(va, vb) => {
            // concretely evaluate
            Some(ctx.bv_lit(&va.get(ctx).and(&vb.get(ctx))))
        }
        Lits::One((lit, lit_expr), expr) => {
            if lit.get(ctx).is_zero() {
                // a & 0 -> 0
                Some(lit_expr)
            } else if lit.get(ctx).is_all_ones() {
                // a & 1 -> a
                Some(expr)
            } else {
                // (a # b) & mask -> ((a & mask_upper) # (b & mask_lower))
                if let Expr::BVConcat(a, b, width) = ctx[expr].clone() {
                    let b_width = b.get_bv_type(ctx).unwrap();
                    debug_assert_eq!(width, b_width + a.get_bv_type(ctx).unwrap());
                    let a_mask = ctx.bv_lit(&lit.get(ctx).slice(width - 1, b_width));
                    let b_mask = ctx.bv_lit(&lit.get(ctx).slice(b_width - 1, 0));
                    Some(ctx.build(|c| c.concat(c.and(a, a_mask), c.and(b, b_mask))))
                } else {
                    // deal with bit mask
                    let width = expr.get_bv_type(ctx).unwrap();
                    let ones = lit.get(ctx).bit_set_intervals();
                    debug_assert!(!ones.is_empty());
                    let mut bit = 0;
                    let mut values: SmallVec<[ExprRef; 6]> = smallvec![];
                    for interval in ones.into_iter() {
                        if interval.start > bit {
                            // zero
                            values.push(ctx.zero(interval.start - bit));
                        }
                        // slice
                        values.push(ctx.slice(expr, interval.end - 1, interval.start));
                        // remember end of slice
                        bit = interval.end;
                    }
                    // zero at the end?
                    if bit < width {
                        values.push(ctx.zero(width - bit));
                    }
                    debug_assert!(values.len() > 1);

                    // the values are in the wrong order, so we need to reverse them
                    let out = values
                        .into_iter()
                        .rev()
                        .reduce(|a, b| ctx.concat(a, b))
                        .unwrap();
                    Some(out)
                }
            }
        }
        Lits::None => {
            match (&ctx[a], &ctx[b]) {
                // a & !a -> 0
                (Expr::BVNot(inner, w), _) if *inner == b => Some(ctx.zero(*w)),
                (_, Expr::BVNot(inner, w)) if *inner == a => Some(ctx.zero(*w)),
                // !a & !b -> !(a | b)
                (Expr::BVNot(a, _), Expr::BVNot(b, _)) => {
                    let or = ctx.or(*a, *b);
                    Some(ctx.not(or))
                }
                _ => None,
            }
        }
    }
}

fn simplify_bv_or(ctx: &mut Context, a: ExprRef, b: ExprRef) -> Option<ExprRef> {
    // a | a -> a
    if a == b {
        return Some(a);
    }

    // other simplifications depend on whether one or two of the values are a constant
    match find_lits_commutative(ctx, a, b) {
        Lits::Two(va, vb) => {
            // concretely evaluate
            Some(ctx.bv_lit(&va.get(ctx).or(&vb.get(ctx))))
        }
        Lits::One((lit, lit_expr), expr) => {
            if lit.get(ctx).is_zero() {
                // a | 0 -> a
                Some(expr)
            } else if lit.get(ctx).is_all_ones() {
                // a | 1 -> 1
                Some(lit_expr)
            } else {
                None
            }
        }
        Lits::None => {
            match (&ctx[a], &ctx[b]) {
                // a | !a -> 1
                (Expr::BVNot(inner, w), _) if *inner == b => Some(ctx.ones(*w)),
                (_, Expr::BVNot(inner, w)) if *inner == a => Some(ctx.ones(*w)),
                // !a | !b -> !(a & b)
                (Expr::BVNot(a, _), Expr::BVNot(b, _)) => {
                    let and = ctx.and(*a, *b);
                    Some(ctx.not(and))
                }
                // sum of products form
                (Expr::BVAnd(a1, b1, _), Expr::BVAnd(a2, b2, _)) => {
                    simplify_sum_of_products(ctx, *a1, *b1, *a2, *b2)
                }
                _ => None,
            }
        }
    }
}

// simplifies some sum of products expressions over exactly two products of t variables
fn simplify_sum_of_products(
    ctx: &mut Context,
    a1: ExprRef,
    b1: ExprRef,
    a2: ExprRef,
    b2: ExprRef,
) -> Option<ExprRef> {
    // recognize a / !a
    let mut lits_1 = [Lit::from_expr(ctx, a1), Lit::from_expr(ctx, b1)];
    let mut lits_2 = [Lit::from_expr(ctx, a2), Lit::from_expr(ctx, b2)];
    // sort by inner expression in order to normalize the order since AND is commutative
    lits_1.sort_by_key(|l| l.get_var());
    lits_2.sort_by_key(|l| l.get_var());
    // define a and b
    let a = lits_1[0].get_var();
    let b = lits_1[1].get_var();
    // check that the second product also is over the same a and b
    if a == lits_2[0].get_var() && b == lits_2[1].get_var() {
        let prod_1 = (lits_1[0].is_neg(), lits_1[1].is_neg());
        let prod_2 = (lits_2[0].is_neg(), lits_2[1].is_neg());
        // sort products
        let mut prods = [prod_1, prod_2];
        prods.sort();

        match (prods[0], prods[1]) {
            // !a & b | a & !b
            ((false, true), (true, false)) => Some(ctx.xor(a, b)),
            // !a & !b | a & b
            // TODO: this currently cannot be triggered, because !a & !b gets converted with demorgan first!
            ((false, false), (true, true)) => Some(ctx.equal(a, b)),
            _ => None,
        }
    } else {
        None
    }
}

#[derive(Debug, Copy, Clone)]
enum Lit {
    Pos(ExprRef),
    Neg(ExprRef),
}

impl Lit {
    fn from_expr(ctx: &Context, e: ExprRef) -> Self {
        if let Expr::BVNot(a, _) = &ctx[e] {
            Lit::Neg(*a)
        } else {
            Lit::Pos(e)
        }
    }
    fn get_var(&self) -> ExprRef {
        match self {
            Lit::Pos(e) => *e,
            Lit::Neg(e) => *e,
        }
    }

    fn is_neg(&self) -> bool {
        matches!(self, Lit::Neg(_))
    }
}

fn simplify_bv_xor(ctx: &mut Context, a: ExprRef, b: ExprRef) -> Option<ExprRef> {
    // a xor a -> 0
    if a == b {
        let width = ctx[a].get_bv_type(ctx).unwrap();
        return Some(ctx.zero(width));
    }

    // other simplifications depend on whether one or two of the values are a constant
    match find_lits_commutative(ctx, a, b) {
        Lits::Two(va, vb) => {
            // concretely evaluate
            Some(ctx.bv_lit(&va.get(ctx).xor(&vb.get(ctx))))
        }
        Lits::One((lit, _), expr) => {
            if lit.get(ctx).is_zero() {
                // a xor 0 -> a
                Some(expr)
            } else if lit.get(ctx).is_all_ones() {
                // a xor 1 -> !a
                Some(ctx.not(expr))
            } else {
                None
            }
        }
        Lits::None => {
            match (&ctx[a], &ctx[b]) {
                // a xor !a -> 1
                (Expr::BVNot(inner, w), _) if *inner == b => Some(ctx.ones(*w)),
                (_, Expr::BVNot(inner, w)) if *inner == a => Some(ctx.ones(*w)),
                _ => None,
            }
        }
    }
}

fn simplify_bv_implies(ctx: &mut Context, a: ExprRef, b: ExprRef) -> Option<ExprRef> {
    // implies(a, b) is equivalent to not(a) or b
    // Check if premise (a) is a constant
    if let Expr::BVLiteral(va) = ctx[a] {
        if va.get(ctx).is_false() {
            // implies(false, _) -> true
            return Some(ctx.get_true());
        } else {
            // implies(true, b) -> b
            return Some(b);
        }
    }

    None
}

fn simplify_bv_greater_equal(ctx: &mut Context, a: ExprRef, b: ExprRef) -> Option<ExprRef> {
    // If both operands are literals, evaluate on the spot
    match (&ctx[a], &ctx[b]) {
        (Expr::BVLiteral(va), Expr::BVLiteral(vb)) => {
            let result = va.get(ctx).is_greater_or_equal(&vb.get(ctx));
            Some(ctx.bv_lit(&result.into()))
        }
        _ => None,
    }
}

fn simplify_bv_not(ctx: &mut Context, e: ExprRef) -> Option<ExprRef> {
    match &ctx[e] {
        Expr::BVNot(inner, _) => Some(*inner), // double negation
        Expr::BVLiteral(value) => Some(ctx.bv_lit(&value.get(ctx).not())),
        _ => None,
    }
}

fn simplify_bv_zero_ext(ctx: &mut Context, e: ExprRef, by: WidthInt) -> Option<ExprRef> {
    if by == 0 {
        Some(e)
    } else {
        match &ctx[e] {
            // zero extend constant
            Expr::BVLiteral(value) => Some(ctx.bv_lit(&value.get(ctx).zero_extend(by))),
            // normalize to concat(${by}'d0, e);
            _ => Some(ctx.build(|c| c.concat(c.zero(by), e))),
        }
    }
}

fn simplify_bv_sign_ext(ctx: &mut Context, e: ExprRef, by: WidthInt) -> Option<ExprRef> {
    if by == 0 {
        Some(e)
    } else {
        match &ctx[e] {
            Expr::BVLiteral(value) => Some(ctx.bv_lit(&value.get(ctx).sign_extend(by))),
            Expr::BVSignExt {
                e: inner_e,
                by: inner_by,
                ..
            } => Some(ctx.sign_extend(*inner_e, by + inner_by)),
            _ => None,
        }
    }
}

fn simplify_bv_concat(ctx: &mut Context, a: ExprRef, b: ExprRef) -> Option<ExprRef> {
    match (ctx[a].clone(), ctx[b].clone()) {
        // normalize concat to be right recursive
        (Expr::BVConcat(a_a, a_b, _), _) => Some(ctx.build(|c| c.concat(a_a, c.concat(a_b, b)))),
        (Expr::BVLiteral(va), Expr::BVLiteral(vb)) => {
            Some(ctx.bv_lit(&va.get(ctx).concat(&vb.get(ctx))))
        }
        (Expr::BVLiteral(va), Expr::BVConcat(b_a, b_b, _)) => {
            if let Expr::BVLiteral(v_b_a) = ctx[b_a] {
                let lit = ctx.bv_lit(&va.get(ctx).concat(&v_b_a.get(ctx)));
                Some(ctx.concat(lit, b_b))
            } else {
                None
            }
        }
        (
            Expr::BVSlice {
                e: a,
                hi: hi_a,
                lo: lo_a,
            },
            Expr::BVSlice {
                e: b,
                hi: hi_b,
                lo: lo_b,
            },
        ) => {
            // slice of the same thing + adjacent
            if a == b && lo_a == hi_b + 1 {
                Some(ctx.slice(a, hi_a, lo_b))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn simplify_bv_slice(ctx: &mut Context, e: ExprRef, hi: WidthInt, lo: WidthInt) -> Option<ExprRef> {
    debug_assert!(hi >= lo);
    match ctx[e].clone() {
        // combine slices
        Expr::BVSlice {
            lo: inner_lo,
            e: inner_e,
            ..
        } => Some(ctx.slice(inner_e, hi + inner_lo, lo + inner_lo)),
        // slice constant
        Expr::BVLiteral(value) => Some(ctx.bv_lit(&value.get(ctx).slice(hi, lo))),
        // slice concat
        Expr::BVConcat(a, b, _) => {
            let b_width = b.get_bv_type(ctx).unwrap();
            if hi < b_width {
                // the slice only includes b
                Some(ctx.slice(b, hi, lo))
            } else if lo >= b_width {
                // the slice only includes a
                Some(ctx.slice(a, hi - b_width, lo - b_width))
            } else {
                // both a and b are included
                let a_slice = ctx.slice(a, hi - b_width, 0);
                let b_slice = ctx.slice(b, b_width - 1, lo);
                Some(ctx.concat(a_slice, b_slice))
            }
        }
        // slice of sign extend
        Expr::BVSignExt { e, .. } => {
            let e_width = e.get_bv_type(ctx).unwrap();
            if hi < e_width {
                Some(ctx.slice(e, hi, lo))
            } else {
                let inner = ctx.slice(e, e_width - 1, lo);
                Some(ctx.sign_extend(inner, hi - e_width + 1))
            }
        }
        // slice of ite
        Expr::BVIte { cond, tru, fals } => {
            Some(ctx.build(|c| c.ite(cond, c.slice(tru, hi, lo), c.slice(fals, hi, lo))))
        }
        // slice of not
        Expr::BVNot(e, _) => Some(ctx.build(|c| c.not(c.slice(e, hi, lo)))),
        // slice of neg
        Expr::BVNegate(e, _) if lo == 0 => Some(ctx.build(|c| c.negate(c.slice(e, hi, lo)))),
        // slice of bit-wise ops
        Expr::BVAnd(a, b, _) => Some(ctx.build(|c| c.and(c.slice(a, hi, lo), c.slice(b, hi, lo)))),
        Expr::BVOr(a, b, _) => Some(ctx.build(|c| c.or(c.slice(a, hi, lo), c.slice(b, hi, lo)))),
        Expr::BVXor(a, b, _) => Some(ctx.build(|c| c.xor(c.slice(a, hi, lo), c.slice(b, hi, lo)))),
        // these ops have information flow from low to high bits
        Expr::BVAdd(a, b, _) if lo == 0 => {
            Some(ctx.build(|c| c.add(c.slice(a, hi, lo), c.slice(b, hi, lo))))
        }
        Expr::BVSub(a, b, _) if lo == 0 => {
            Some(ctx.build(|c| c.sub(c.slice(a, hi, lo), c.slice(b, hi, lo))))
        }
        Expr::BVMul(a, b, _) if lo == 0 => {
            Some(ctx.build(|c| c.mul(c.slice(a, hi, lo), c.slice(b, hi, lo))))
        }

        _ => None,
    }
}

fn simplify_bv_shift_left(
    ctx: &mut Context,
    a: ExprRef,
    b: ExprRef,
    width: WidthInt,
) -> Option<ExprRef> {
    match (&ctx[a], &ctx[b]) {
        (Expr::BVLiteral(va), Expr::BVLiteral(vb)) => {
            Some(ctx.bv_lit(&va.get(ctx).shift_left(&vb.get(ctx))))
        }
        (_, Expr::BVLiteral(by)) => {
            let by = by.get(ctx);
            if let Some(by) = by.to_u64() {
                let by = by as WidthInt;
                if by >= width {
                    Some(ctx.zero(width))
                } else if by == 0 {
                    Some(a)
                } else {
                    let msb = width - 1 - by;
                    Some(ctx.build(|c| c.concat(c.slice(a, msb, 0), c.zero(by))))
                }
            } else {
                Some(ctx.zero(width))
            }
        }
        (_, _) => None,
    }
}

fn simplify_bv_shift_right(
    ctx: &mut Context,
    a: ExprRef,
    b: ExprRef,
    width: WidthInt,
) -> Option<ExprRef> {
    match (&ctx[a], &ctx[b]) {
        (Expr::BVLiteral(va), Expr::BVLiteral(vb)) => {
            Some(ctx.bv_lit(&va.get(ctx).shift_right(&vb.get(ctx))))
        }
        (_, Expr::BVLiteral(by)) => {
            let by = by.get(ctx);
            if let Some(by) = by.to_u64() {
                let by = by as WidthInt;
                if by >= width {
                    Some(ctx.zero(width))
                } else if by == 0 {
                    Some(a)
                } else {
                    let msb = width - 1;
                    let lsb = by;
                    Some(ctx.build(|c| c.zero_extend(c.slice(a, msb, lsb), by)))
                }
            } else {
                Some(ctx.zero(width))
            }
        }
        (_, _) => None,
    }
}

fn simplify_bv_arithmetic_shift_right(
    ctx: &mut Context,
    a: ExprRef,
    b: ExprRef,
    width: WidthInt,
) -> Option<ExprRef> {
    match (&ctx[a], &ctx[b]) {
        (Expr::BVLiteral(va), Expr::BVLiteral(vb)) => {
            Some(ctx.bv_lit(&va.get(ctx).arithmetic_shift_right(&vb.get(ctx))))
        }
        (_, Expr::BVLiteral(by)) => {
            let by = by.get(ctx);
            if let Some(by) = by.to_u64() {
                let by = by as WidthInt;
                if by >= width {
                    Some(ctx.build(|c| c.sign_extend(c.slice(a, width - 1, width - 1), width - 1)))
                } else if by == 0 {
                    Some(a)
                } else {
                    let msb = width - 1;
                    let lsb = by;
                    Some(ctx.build(|c| c.sign_extend(c.slice(a, msb, lsb), by)))
                }
            } else {
                Some(ctx.build(|c| c.sign_extend(c.slice(a, width - 1, width - 1), width - 1)))
            }
        }
        (_, _) => None,
    }
}

fn simplify_bv_add(ctx: &mut Context, a: ExprRef, b: ExprRef) -> Option<ExprRef> {
    match find_lits_commutative(ctx, a, b) {
        Lits::Two(va, vb) => Some(ctx.bv_lit(&va.get(ctx).add(&vb.get(ctx)))),
        Lits::One((va, _), b) => {
            if va.get(ctx).is_zero() {
                Some(b)
            } else {
                None
            }
        }
        Lits::None => None,
    }
}

fn simplify_bv_mul(ctx: &mut Context, a: ExprRef, b: ExprRef) -> Option<ExprRef> {
    match find_lits_commutative(ctx, a, b) {
        Lits::Two(va, vb) => Some(ctx.bv_lit(&va.get(ctx).mul(&vb.get(ctx)))),
        Lits::One((va, a), b) => {
            let va = va.get(ctx);
            if va.is_zero() {
                // b * 0 -> 0
                Some(a)
            } else if va.is_one() {
                // b * 1 -> b
                Some(b)
            } else if let Some(log_2) = va.is_pow_2() {
                // b * 2**log_2 -> b
                let log_2 = ctx.bit_vec_val(log_2, va.width());
                Some(ctx.shift_left(b, log_2))
            } else {
                None
            }
        }
        Lits::None => None,
    }
}
