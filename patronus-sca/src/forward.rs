// Copyright 2026 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Forward Polynomial Creation
//! Starts at the inputs and builds up the polynomial bottom up.

use crate::{Poly, expr_to_var, extract_bit};
use baa::{BitVecOps, BitVecValueRef};
use patronus::expr::{
    Context, Expr, ExprRef, ExprSet, ForEachChild, SerializableIrNode, SparseExprMap,
    SparseExprSet, TypeCheck, count_expr_uses, traversal,
};
use polysub::{Coef, Mod};
use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Debug, Copy, Clone)]
pub enum BuildPolyMode {
    Arithmetic,
    Gates(Mod),
}

/// Returns a polynomial representation of the expression + all input expressions if possible.
/// Returns `None` if the conversion fails.
pub fn build_bottom_up_poly(
    ctx: &mut Context,
    inputs: &FxHashSet<ExprRef>,
    e: ExprRef,
    mode: BuildPolyMode,
) -> Option<Poly> {
    // we use a custom traversal that caches polynomials until they are no longer used
    let mut uses = count_expr_uses(ctx, vec![e]);
    let mut todo = vec![e];
    let mut result: FxHashMap<ExprRef, Option<(Poly, bool)>> = FxHashMap::default();
    let mut child_vec = Vec::with_capacity(4);

    while let Some(e) = todo.pop() {
        assert!(!result.contains_key(&e));

        let expr = &ctx[e];
        // find children that are not available yet.
        debug_assert!(child_vec.is_empty());
        expr.collect_children(&mut child_vec);
        let all_available = child_vec.iter().all(|c| result.contains_key(c));

        if all_available {
            let child_results: Vec<Option<&(Poly, bool)>> =
                child_vec.iter().map(|c| result[c].as_ref()).collect();
            let r = to_poly(ctx, inputs, mode, e, &child_results);
            result.insert(e, r);
            for child in child_vec.drain(..) {
                let old_use = uses[child];
                if old_use == 1 {
                    result.remove(&child);
                }
                uses[child] = old_use - 1;
            }
        } else {
            todo.push(e);
            for child in child_vec.drain(..) {
                if !result.contains_key(&child) {
                    todo.push(child);
                }
            }
        }
    }

    result[&e].as_ref().map(|(p, _)| p.clone())
}

fn to_poly(
    ctx: &mut Context,
    inputs: &FxHashSet<ExprRef>,
    mode: BuildPolyMode,
    e: ExprRef,
    children: &[Option<&(Poly, bool)>],
) -> Option<(Poly, bool)> {
    // have we given up yet?
    if children.iter().any(|c| c.is_none()) {
        return None;
    }

    // special handle inputs:
    if inputs.contains(&e) {
        return Some((poly_for_bv_expr(ctx, e), false));
    }

    match mode {
        BuildPolyMode::Arithmetic => to_poly_arithmetic(ctx, inputs, e, children),
        BuildPolyMode::Gates(m) => Some((to_poly_gate(ctx, inputs, m, e, children), false)),
    }
}

/// For bit-level polynomials from gates, the normal arithmetic rules and overflow checking do not
/// apply. Instead, we use the modulo coefficient of the top-level expression.
fn to_poly_gate(
    ctx: &mut Context,
    inputs: &FxHashSet<ExprRef>,
    m: Mod,
    e: ExprRef,
    children: &[Option<&(Poly, bool)>],
) -> Poly {
    debug_assert!(
        children
            .iter()
            .all(|c| c.map(|(_, ov)| !*ov).unwrap_or(true))
    );

    match (ctx[e].clone(), children) {
        (Expr::BVSymbol { .. }, _) => unreachable!("all symbols should be in inputs"),
        (Expr::BVLiteral(value), _) => {
            let mut r = poly_for_bv_literal(value.get(ctx));
            r.change_mod(m);
            r
        }
        (Expr::BVSlice { e, hi, lo }, _) if hi == lo && inputs.contains(&e) => {
            // special case: bit_slice of an input
            let var = expr_to_var(extract_bit(ctx, e, hi));
            Poly::from_monoms(m, [(Coef::from_i64(1, m), vec![var].into())].into_iter())
        }
        (Expr::BVConcat(_, be, w), [Some((a, _)), Some((b, _))]) => {
            // left shift a
            let shift_by = be.get_bv_type(ctx).unwrap();
            let shift_coef = Coef::pow2(shift_by, m);
            let mut r: Poly = a.clone();
            r.scale(&shift_coef);
            r.add_assign(b);
            r
        }
        (Expr::BVOr(_, _, 1), [Some((a, _)), Some((b, _))]) => {
            // a + b - ab
            let mut r = a.mul(b);
            r.scale(&Coef::from_i64(-1, a.get_mod()));
            r.add_assign(a);
            r.add_assign(b);
            r
        }
        (Expr::BVXor(_, _, 1), [Some((a, _)), Some((b, _))]) => {
            // a + b - 2ab
            let mut r = a.mul(b);
            let minus_2 = Coef::from_i64(-2, a.get_mod());
            r.scale(&minus_2);
            r.add_assign(a);
            r.add_assign(b);
            r
        }
        (Expr::BVAnd(_, _, 1), [Some((a, _)), Some((b, _))]) => {
            // ab
            a.clone().mul(b)
        }
        (Expr::BVNot(_, 1), [Some((a, _))]) => {
            // 1 - a
            let one = Poly::from_monoms(m, [(Coef::from_i64(1, m), vec![].into())].into_iter());
            let mut r = a.clone();
            r.scale(&Coef::from_i64(-1, a.get_mod()));
            r.add_assign(&one);
            r
        }
        (other, cs) => todo!("{other:?}: {cs:?}"),
    }
}

/// When building a polynomial over an arithmetic circuit, we are tracking overflow and
/// determining the modulo coefficient from the bit-widths.
fn to_poly_arithmetic(
    ctx: &mut Context,
    _inputs: &FxHashSet<ExprRef>,
    e: ExprRef,
    children: &[Option<&(Poly, bool)>],
) -> Option<(Poly, bool)> {
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
