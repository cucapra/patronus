// Copyright 2026 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::{DefaultCoef, Poly, expr_to_var};
use baa::BitVecOps;
use patronus::expr::{
    Context, DenseExprSet, Expr, ExprRef, ExprSet, ForEachChild, count_expr_uses,
};
use polysub::{PhaseOptPolynom, VarIndex};
use rustc_hash::FxHashSet;
use std::collections::VecDeque;

/// Used for backwards substitution
type PolyOpt = polysub::PhaseOptPolynom<DefaultCoef>;

pub fn backwards_sub(
    ctx: &Context,
    input_vars: &FxHashSet<VarIndex>,
    todo: Vec<(VarIndex, ExprRef)>,
    spec: Poly,
) -> Poly {
    // empirically, it looks like we should not use a stack
    let mut todo: VecDeque<_> = todo.into();
    let mut spec: PolyOpt = spec.into();
    let mut var_roots: Vec<_> = todo.iter().map(|(v, _)| *v).collect();
    var_roots.sort();

    // first, we count how often expressions are used
    let roots: Vec<_> = todo.iter().map(|(_, e)| *e).collect();
    let mut uses = count_expr_uses(ctx, roots);
    let mut replaced = vec![];
    let mut seen = DenseExprSet::default();

    while !todo.is_empty() {
        //try_exhaustive(ctx, input_vars, &spec, todo.iter().cloned());

        // chose variable to replace
        let (output_var, gate) = todo.pop_back().unwrap();

        replaced.push(output_var);
        println!(
            "{output_var} {:?}: {}, {}",
            &ctx[gate],
            todo.len() + 1,
            spec.size()
        );

        let add_children = replace_gate(ctx, input_vars, &mut spec, output_var, gate);

        if add_children {
            ctx[gate].for_each_child(|&e| {
                // reduce the use by one
                let prev_uses = uses[e];
                assert!(prev_uses > 0);
                uses[e] = prev_uses - 1;
                // did the use count just go down to zero?
                let var = expr_to_var(e);
                if prev_uses == 1 && !input_vars.contains(&var) {
                    todo.push_back((var, e));
                } else if !seen.contains(&e) {
                    // try phase opt
                    let old_size = spec.size();
                    spec.invert(var);
                    if spec.size() > old_size {
                        spec.invert(var);
                    } else {
                        println!("INVERTING {var} {old_size} -> {}", spec.size());
                    }
                }
                seen.insert(e);
            });
        }
    }

    println!("Roots: {var_roots:?}");

    replaced.sort();
    println!("Replaced variables: {replaced:?}");

    // find any expressions where uses are not zero
    use patronus::expr::ExprMap;
    let mut still_used: Vec<_> = uses
        .iter()
        .filter(|(_, v)| **v > 0)
        .map(|(k, _)| expr_to_var(k))
        .collect();
    still_used.sort();
    println!("Still used: {still_used:?}");

    let spec: Poly = spec.into();
    let mut remaining_vars: Vec<_> = spec
        .sorted_monom_vec()
        .iter()
        .flat_map(|(_, t)| t.vars().cloned().collect::<Vec<_>>())
        .collect();
    remaining_vars.sort();
    remaining_vars.dedup();
    println!("Remaining vars: {remaining_vars:?}");

    spec
}

fn replace_gate(
    ctx: &Context,
    input_vars: &FxHashSet<VarIndex>,
    spec: &mut PolyOpt,
    output_var: VarIndex,
    gate: ExprRef,
) -> bool {
    match ctx[gate].clone() {
        Expr::BVOr(a, b, 1) => {
            spec.replace_or(output_var, expr_to_var(a), expr_to_var(b));
            true
        }
        Expr::BVXor(a, b, 1) => {
            spec.replace_xor(output_var, expr_to_var(a), expr_to_var(b));
            true
        }
        Expr::BVAnd(a, b, 1) => {
            spec.replace_and(output_var, expr_to_var(a), expr_to_var(b));
            true
        }
        Expr::BVNot(a, 1) => {
            spec.replace_not(output_var, expr_to_var(a));
            true
        }
        Expr::BVSlice { hi, lo, e } => {
            assert_eq!(hi, lo);
            assert!(
                input_vars.contains(&expr_to_var(e)),
                "Not actually an input: {e:?}"
            );
            // a bit slice normally marks an input, thus we should be done!
            false
        }
        Expr::BVLiteral(value) => {
            let value = value.get(ctx);
            debug_assert_eq!(value.width(), 1);
            if value.is_true() {
                spec.replace_true(output_var);
            } else {
                spec.replace_false(output_var);
            }
            false
        }
        other => todo!("add support for {other:?}"),
    }
}

fn try_exhaustive(
    ctx: &Context,
    input_vars: &FxHashSet<VarIndex>,
    spec: &PolyOpt,
    todo: impl Iterator<Item = (VarIndex, ExprRef)>,
) {
    for (ii, (output_var, gate)) in todo.enumerate() {
        let mut s = spec.clone();
        replace_gate(ctx, input_vars, &mut s, output_var, gate);
        println!(
            "  {ii:>3}: {output_var} {:?}: {} -> {}",
            &ctx[gate],
            spec.size(),
            s.size()
        );
    }
}
