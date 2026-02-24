// Copyright 2026 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Forward Polynomial Creation
//! Starts at the inputs and builds up the polynomial bottom up.

use crate::{Poly, expr_to_var, extract_bit};
use baa::{BitVecOps, BitVecValueRef};
use patronus::expr::{Context, Expr, ExprRef, ExprSet, SparseExprSet, TypeCheck, traversal};
use polysub::Coef;
use rustc_hash::FxHashSet;

/// Returns a polynomial representation of the expression + all input expressions if possible.
/// Returns `None` if the conversion fails.
pub fn build_bottom_up_poly(
    ctx: &mut Context,
    inputs: &FxHashSet<ExprRef>,
    e: ExprRef,
) -> Option<Poly> {
    traversal::bottom_up_mut(ctx, e, |ctx, e, c| to_poly(ctx, inputs, e, c)).map(|(p, _)| p)
}

fn to_poly(
    ctx: &mut Context,
    inputs: &FxHashSet<ExprRef>,
    e: ExprRef,
    children: &[Option<(Poly, bool)>],
) -> Option<(Poly, bool)> {
    // have we given up yet?
    if children.iter().any(|c| c.is_none()) {
        return None;
    }

    // special handle inputs:
    if inputs.contains(&e) {
        return Some((poly_for_bv_expr(ctx, e), false));
    }

    match (ctx[e].clone(), children) {
        (Expr::BVSymbol { .. }, _) => unreachable!("all symbols should be in inputs"),
        (Expr::BVLiteral(value), _) => Some((poly_for_bv_literal(value.get(ctx)), false)),
        (Expr::BVConcat(_, _, w), [Some((a, ao)), Some((b, bo))]) => {
            // if b may have overflowed, then we cannot perform the concatenation
            if *bo {
                return None;
            }

            // left shift a
            let shift_by = b.get_mod().bits();
            let result_width = a.get_mod().bits() + shift_by;
            debug_assert_eq!(
                result_width, w,
                "smt expr result type does not match polynomial mod coefficient"
            );
            let new_m = polysub::Mod::from_bits(result_width);
            let shift_coef = Coef::pow2(shift_by, new_m);
            let mut r: Poly = a.clone();
            r.change_mod(new_m);
            r.scale(&shift_coef);
            // add b
            let mut b = b.clone();
            b.change_mod(new_m); // TODO: allow adding without changing the mod of b to avoid this copy
            r.add_assign(&b);
            Some((r, *ao || *bo))
        }
        (Expr::BVZeroExt { by, .. }, [Some((b, bo))]) => {
            // if b may have overflowed, then we cannot perform the concatenation
            if *bo {
                return None;
            }

            let result_width = b.get_mod().bits() + by;
            let new_m = polysub::Mod::from_bits(result_width);
            let mut r: Poly = b.clone();
            r.change_mod(new_m);
            Some((r, *bo))
        }
        (Expr::BVAdd(ae, be, w), [Some((a, ao)), Some((b, bo))]) => {
            debug_assert_eq!(w, a.get_mod().bits());
            debug_assert_eq!(w, b.get_mod().bits());
            let mut r = a.clone();
            r.add_assign(b);
            Some((r, *ao || *bo))
        }
        (Expr::BVMul(ae, be, w), [Some((a, ao)), Some((b, bo))]) => {
            debug_assert_eq!(w, a.get_mod().bits());
            debug_assert_eq!(w, b.get_mod().bits());
            let r = a.mul(b);
            Some((r, *ao || *bo))
        }
        (Expr::BVNegate(_, w), [Some((e, eo))]) => {
            println!("TODO: add support for negate!");
            None
        }
        (other, cs) => todo!("{other:?}: {cs:?}"),
    }
}

fn poly_for_bv_literal(value: BitVecValueRef) -> Poly {
    let m = polysub::Mod::from_bits(value.width());
    // we need to convert the value into a coefficient
    let big_value = value.to_big_int();
    let coef = Coef::from_big(&big_value, m);
    // now we create a polynomial with just this coefficient
    let monom = (coef, vec![].into());
    Poly::from_monoms(m, vec![monom].into_iter())
}

pub fn poly_for_bv_expr(ctx: &mut Context, e: ExprRef) -> Poly {
    let width = e
        .get_bv_type(ctx)
        .expect("function only works with bitvector expressions.");
    let m = polysub::Mod::from_bits(width);
    Poly::from_monoms(
        m,
        (0..width).map(|ii| {
            // add an entry for each bit
            let bit_expr = extract_bit(ctx, e, ii);
            let bit_var = expr_to_var(bit_expr);
            let term: polysub::Term = vec![bit_var].into();
            let coef = Coef::pow2(ii, m);
            (coef, term)
        }),
    )
}
