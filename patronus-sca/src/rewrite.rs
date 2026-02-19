// Copyright 2026 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::{DefaultCoef, Poly, expr_to_var};
use baa::BitVecOps;
use bit_set::BitSet;
use patronus::expr::{
    Context, DenseExprMetaData, DenseExprSet, Expr, ExprMap, ExprRef, ExprSet, ForEachChild,
    SerializableIrNode, count_expr_uses, traversal,
};
use polysub::{Coef, Mod, PhaseOptPolynom, VarIndex};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::VecDeque;

/// Used for backwards substitution
type PolyOpt = PhaseOptPolynom<DefaultCoef>;

pub fn backwards_sub(
    ctx: &Context,
    input_vars: &FxHashSet<VarIndex>,
    todo: Vec<(VarIndex, ExprRef)>,
    gate_level_expr: ExprRef,
    spec: Poly,
) -> Poly {
    let root_vars: Vec<_> = todo.iter().map(|(v, _)| *v).collect();
    let root_exprs: Vec<_> = todo.iter().map(|(_, e)| *e).collect();
    let root_uses = analyze_uses(ctx, &root_exprs);

    let gate_count = print_gate_stats(ctx, input_vars, gate_level_expr);

    // check to see if there are any half adders we can identify
    let has = find_half_adders(ctx, gate_level_expr);
    println!("HAs: {has:?}");
    let fas = find_full_adders(ctx, gate_level_expr);

    let same_input = find_expr_with_same_inputs(ctx, gate_level_expr);
    println!("Expressions that have the same input:");
    for (a, b) in same_input {
        println!("{:?} and {:?}", &ctx[a], &ctx[b]);
    }

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

    let mut iter_count = 0;
    while !todo.is_empty() {
        iter_count += 1;
        //let gate_idx = try_exhaustive(ctx, input_vars, &spec, todo.iter().cloned(), &root_uses);
        // println!("CHOICE: {todo:?}");
        let gate_idx = pick_smallest_use(todo.iter().cloned(), &root_uses);
        let (output_var, gate) = todo.swap_remove_back(gate_idx).unwrap();

        // chose variable to replace
        //let (output_var, gate) = todo.pop_back().unwrap();

        replaced.push(output_var);
        let gate_uses = &root_uses[gate];
        let num_output_uses = gate_uses.len();
        let output_use_str = gate_uses
            .iter()
            .map(|ii| format!("{}", root_vars[ii]))
            .collect::<Vec<_>>()
            .join(", ");
        println!(
            "{iter_count}/{gate_count} {output_var} ({output_use_str}) {:?}: {}, {}",
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

fn print_gate_stats(ctx: &Context, input_vars: &FxHashSet<VarIndex>, root: ExprRef) -> u32 {
    let mut ands = 0u32;
    let mut xors = 0u32;
    let mut ors = 0u32;
    let mut nots = 0u32;
    let mut ones = 0u32;
    let mut zeros = 0u32;
    let mut seen = DenseExprSet::default();
    traversal::bottom_up(ctx, root, |ctx, e, _| {
        if input_vars.contains(&expr_to_var(e)) || seen.contains(&e) {
            return;
        }
        seen.insert(e);
        match &ctx[e] {
            Expr::BVOr(_, _, 1) => ors += 1,
            Expr::BVXor(_, _, 1) => xors += 1,
            Expr::BVAnd(_, _, 1) => ands += 1,
            Expr::BVNot(_, 1) => nots += 1,
            Expr::BVLiteral(value) => {
                let value = value.get(ctx);
                debug_assert_eq!(value.width(), 1);
                if value.is_true() {
                    ones += 1;
                } else {
                    zeros += 1;
                }
            }
            _ => {} // ignore
        }
    });
    println!("AND: {ands}, XOR: {xors}, OR: {ors}, NOT: {nots}, 1: {ones}, 0: {zeros}");
    ands + xors + ors + nots + ones + zeros
}

fn pick_smallest_use(
    todo: impl Iterator<Item = (VarIndex, ExprRef)>,
    root_uses: &impl ExprMap<BitSet>,
) -> usize {
    let uses: Vec<_> = todo.map(|(_, gate)| root_uses[gate].len()).collect();
    let min_uses = *uses.iter().min().unwrap();
    uses.iter().position(|u| *u == min_uses).unwrap()
}

fn try_exhaustive(
    ctx: &Context,
    input_vars: &FxHashSet<VarIndex>,
    spec: &PolyOpt,
    todo: impl Iterator<Item = (VarIndex, ExprRef)>,
    root_uses: &impl ExprMap<BitSet>,
) -> usize {
    let sizes: Vec<_> = todo
        .enumerate()
        .map(|(ii, (output_var, gate))| {
            let mut s = spec.clone();
            replace_gate(ctx, input_vars, &mut s, output_var, gate);
            (s.size(), root_uses[gate].len())
        })
        .collect();
    let min = sizes.iter().map(|(s, _)| *s).min().unwrap();
    let max = sizes.iter().map(|(s, _)| *s).max().unwrap();
    let all_mins: Vec<_> = sizes.iter().filter(|(s, _)| *s == min).collect();
    let lowest_min_use = all_mins.iter().map(|(_, u)| *u).min().unwrap();
    let min_with_lowest_use = sizes
        .iter()
        .position(|(s, u)| *s == min && *u == lowest_min_use)
        .unwrap();
    println!(
        "{} -> {min}/{max}, {} mins, lowest use: {lowest_min_use}",
        spec.size(),
        all_mins.len()
    );
    min_with_lowest_use
}

/// tries to build the gate-level polynomial from the bottom up.
pub fn build_gate_polynomial(
    ctx: &Context,
    input_vars: &FxHashSet<VarIndex>,
    m: Mod,
    e: ExprRef,
) -> Poly {
    traversal::bottom_up(ctx, e, |ctx, gate, children: &[Poly]| {
        let var = expr_to_var(gate);

        // if this is an input, we just want to return the variable
        if input_vars.contains(&var) {
            return Poly::from_monoms(m, [(Coef::from_i64(1, m), vec![var].into())].into_iter());
        }

        match (ctx[gate].clone(), children) {
            (Expr::BVOr(_, _, 1), [a, b]) => {
                // a + b - ab
                let mut r = a.mul(b);
                r.scale(&Coef::from_i64(-1, m));
                r.add_assign(a);
                r.add_assign(b);
                r
            }
            (Expr::BVXor(_, _, 1), [a, b]) => {
                // a + b - 2ab
                let mut r = a.mul(b);
                r.scale(&Coef::from_i64(-2, m));
                r.add_assign(a);
                r.add_assign(b);
                r
            }
            (Expr::BVAnd(_, _, 1), [a, b]) => {
                // ab
                a.mul(b)
            }
            (Expr::BVNot(_, 1), [a]) => {
                // 1 - a
                let one = Poly::from_monoms(m, [(Coef::from_i64(1, m), vec![].into())].into_iter());
                let mut r = a.clone();
                r.scale(&Coef::from_i64(-1, m));
                r.add_assign(&one);
                r
            }
            (Expr::BVSlice { .. }, [_]) => {
                todo!("should not get here!")
            }
            (Expr::BVLiteral(value), _) => {
                let value = value.get(ctx);
                debug_assert_eq!(value.width(), 1);
                if value.is_true() {
                    Poly::from_monoms(m, [(Coef::from_i64(1, m), vec![].into())].into_iter())
                } else {
                    Poly::from_monoms(m, [(Coef::from_i64(0, m), vec![].into())].into_iter())
                }
            }
            other => todo!("add support for {other:?}"),
        }
    })
}

/// Calculates for each expression which root depends on it.
fn analyze_uses(ctx: &Context, roots: &[ExprRef]) -> impl ExprMap<BitSet> {
    let mut out = DenseExprMetaData::<BitSet>::default();

    for (ii, &root) in roots.iter().enumerate() {
        let mut id = BitSet::new();
        id.insert(ii);
        traversal::bottom_up(ctx, root, |_, e, _| {
            out[e].union_with(&id);
        })
    }

    out
}

#[derive(Debug, Copy, Clone, PartialEq)]
struct HalfAdder {
    a: ExprRef,
    b: ExprRef,
    /// a xor b
    sum: ExprRef,
    /// a and b
    carry: ExprRef,
}

/// Tries to identify two expressions which correspond to "a and b" and "a xor b".
fn find_half_adders(ctx: &Context, gate_level: ExprRef) -> Vec<HalfAdder> {
    let mut xor = FxHashMap::default();
    let mut and = FxHashMap::default();
    traversal::bottom_up(ctx, gate_level, |ctx, e, _| match ctx[e].clone() {
        Expr::BVXor(a, b, 1) => {
            xor.insert(two_expr_key(a, b), e);
        }
        Expr::BVAnd(a, b, 1) => {
            and.insert(two_expr_key(a, b), e);
        }
        _ => {}
    });
    let mut out = vec![];
    for (key, xor_e) in xor.iter() {
        if let Some(and_e) = and.get(key) {
            let (a, b) = key.clone();
            let sum = *xor_e;
            let carry = *and_e;
            out.push(HalfAdder { a, b, sum, carry })
        }
    }
    out
}

#[derive(Debug, Copy, Clone, PartialEq)]
struct FullAdder {
    a: ExprRef,
    b: ExprRef,
    // carry in
    c: ExprRef,
    /// a xor b xor c
    sum: ExprRef,
    /// a and b
    carry: ExprRef,
}

fn find_full_adders(ctx: &Context, gate_level: ExprRef) -> Vec<HalfAdder> {
    let mut xor = FxHashMap::default();
    traversal::bottom_up(ctx, gate_level, |ctx, e, _| match ctx[e].clone() {
        Expr::BVXor(a, b, 1) => {
            let key = if let Expr::BVXor(a1, a2, 1) = ctx[a].clone() {
                Some(three_expr_key(a1, a2, b))
            } else if let Expr::BVXor(b1, b2, 1) = ctx[b].clone() {
                Some(three_expr_key(a, b1, b2))
            } else {
                None
            };
            if let Some(key) = key {
                xor.insert(key, e);
            }
        }
        _ => {}
    });

    println!("Found {} 3-XOR gates", xor.len());
    for v in xor.values() {
        println!("  {}", v.serialize_to_str(ctx));
    }

    let mut out = vec![];
    // TODO
    out
}

fn find_expr_with_same_inputs(ctx: &Context, gate_level: ExprRef) -> Vec<(ExprRef, ExprRef)> {
    let mut others = FxHashMap::default();
    traversal::bottom_up(ctx, gate_level, |ctx, e, _| match ctx[e].clone() {
        Expr::BVXor(a, b, 1) | Expr::BVAnd(a, b, 1) | Expr::BVOr(a, b, 1) => {
            let v = others.entry(two_expr_key(a, b)).or_insert(vec![]);
            if !v.contains(&e) {
                v.push(e);
            }
        }
        _ => {}
    });

    let mut out = vec![];
    for (key, value) in others {
        if value.len() > 1 {
            match value.as_slice() {
                [a, b] => out.push((*a, *b)),
                other => todo!("{other:?}"),
            }
        }
    }
    out
}

/// Sorts the two expressions to generate a unique key
fn two_expr_key(a: ExprRef, b: ExprRef) -> (ExprRef, ExprRef) {
    if usize::from(a) <= usize::from(b) {
        (a, b)
    } else {
        (b, a)
    }
}

/// Sorts three expressions to generate a unique key
fn three_expr_key(a: ExprRef, b: ExprRef, c: ExprRef) -> (ExprRef, ExprRef, ExprRef) {
    let mut all = [a, b, c];
    all.sort_by_key(|e| usize::from(*e));
    (all[0], all[1], all[2])
}
