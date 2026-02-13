// Copyright 2026 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::{BitVecOps, BitVecValue, BitVecValueRef};
use patronus::expr::*;
use polysub::{Coef, Term, VarIndex};
use std::fmt::{Display, Formatter};

/// Returns a new expressions reference if simplification was possible
pub fn simplify_word_level_equality(ctx: &mut Context, p: ScaEqualityProblem) -> Option<ExprRef> {
    let width = p.word_level.get_bv_type(ctx).unwrap();
    debug_assert_eq!(width, p.gate_level.get_bv_type(ctx).unwrap());

    // create a reference polynomial from the word level side
    let mut word_poly = build_bottom_up_poly(ctx, p.word_level);
    println!("word-level polynomial: {word_poly}");

    // the actual reference polynomial needs to contain the output bits as well
    let output_poly = poly_for_bv_expr(ctx, p.word_level);
    word_poly.scale(&Coef::from_i64(-1, word_poly.get_mod()));
    word_poly.add_assign(&output_poly);
    let spec = word_poly;

    // create todos for all output variables
    let gate_outputs: Vec<_> = (0..width)
        .map(|ii| {
            // it is _important_ that we slice the **word-level** output here, so that we get matching
            // variable indices
            let word_bit_expr = extract_bit(ctx, p.word_level, ii);
            let bit_var = expr_to_var(word_bit_expr);
            let gate_bit_expr = extract_bit(ctx, p.gate_level, ii);
            (bit_var, gate_bit_expr)
        })
        .collect();

    // now we can perform backwards substitution
    let result = backwards_sub(ctx, gate_outputs.into(), spec);

    if result.is_zero() {
        println!("The SAME!");
        Some(ctx.get_true())
    } else {
        println!("DIFFERENT: {result}");
        Some(ctx.get_false())
    }
}

/// Extracts a bit from a concatenation. We use this to avoid having to call the full blown
/// simplifier.
fn extract_bit(ctx: &mut Context, e: ExprRef, bit: WidthInt) -> ExprRef {
    match ctx[e].clone() {
        Expr::BVConcat(a, b, _) => {
            let b_width = b.get_bv_type(ctx).unwrap();
            if bit < b_width {
                extract_bit(ctx, b, bit)
            } else {
                extract_bit(ctx, a, bit - b_width)
            }
        }
        _ => ctx.slice(e, bit, bit),
    }
}

type DefaultCoef = polysub::ArrayCoef<8>;
type Poly = polysub::Polynom<DefaultCoef>;

fn expr_to_var(e: ExprRef) -> polysub::VarIndex {
    (usize::from(e) as u32).into()
}

/// converts the two expression references and ensures that the smallest var index is returned first
#[inline]
fn exprs_to_vars_commutative(a: ExprRef, b: ExprRef) -> (VarIndex, VarIndex) {
    let a = expr_to_var(a);
    let b = expr_to_var(b);
    if a > b { (b, a) } else { (a, b) }
}

fn var_to_expr(v: polysub::VarIndex) -> ExprRef {
    usize::from(v).into()
}

fn is_gate(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::BVNot(_, 1) | Expr::BVAnd(_, _, 1) | Expr::BVOr(_, _, 1) | Expr::BVXor(_, _, 1)
    )
}

fn backwards_sub(ctx: &Context, mut todo: Vec<(VarIndex, ExprRef)>, mut spec: Poly) -> Poly {
    let mut var_roots: Vec<_> = todo.iter().map(|(v, _)| *v).collect();
    var_roots.sort();

    let m = spec.get_mod();
    let one: DefaultCoef = Coef::from_i64(1, m);
    let minus_one: DefaultCoef = Coef::from_i64(-1, m);
    let minus_two: DefaultCoef = Coef::from_i64(-2, m);
    // first, we count how often expressions are used
    let roots: Vec<_> = todo.iter().map(|(_, e)| *e).collect();
    let mut uses = count_expr_uses(ctx, roots);
    let mut replaced = vec![];

    let const_true_var = expr_to_var(ctx.get_true());

    while let Some((output_var, gate)) = todo.pop() {
        replaced.push(output_var);
        // println!("{output_var}: {}", spec.size());

        let add_children = match ctx[gate].clone() {
            Expr::BVOr(a, b, 1) => {
                // a + b - ab
                let (x0, x1) = exprs_to_vars_commutative(a, b);
                let monoms = [
                    (one.clone(), vec![x0].into()),
                    (one.clone(), vec![x1].into()),
                    (minus_one.clone(), vec![x0, x1].into()),
                ];
                assert_ne!(gate, a);
                assert_ne!(gate, b);
                spec.replace_var(output_var, &monoms);
                true
            }
            Expr::BVXor(a, b, 1) => {
                // a + b - 2ab
                let (x0, x1) = exprs_to_vars_commutative(a, b);
                let monoms = [
                    (one.clone(), vec![x0].into()),
                    (one.clone(), vec![x1].into()),
                    (minus_two.clone(), vec![x0, x1].into()),
                ];
                assert_ne!(gate, a);
                assert_ne!(gate, b);
                spec.replace_var(output_var, &monoms);
                true
            }
            Expr::BVAnd(a, b, 1) => {
                // ab
                let (x0, x1) = exprs_to_vars_commutative(a, b);
                let monoms = [(one.clone(), vec![x0, x1].into())];
                assert_ne!(gate, a);
                assert_ne!(gate, b);
                spec.replace_var(output_var, &monoms);
                true
            }
            Expr::BVNot(a, 1) => {
                // 1 - a
                let x0 = expr_to_var(a);
                let monoms = [
                    (one.clone(), vec![].into()),
                    (minus_one.clone(), vec![x0].into()),
                ];
                assert_ne!(gate, a);
                spec.replace_var(output_var, &monoms);
                true
            }
            Expr::BVSlice { hi, lo, .. } => {
                assert_eq!(hi, lo);
                // a bit slice normally marks an input, thus we should be done!
                false
            }
            other => todo!("add support for {other:?}"),
        };
        // get rid of any ones, TODO: we should eventually write better code and make this unnecessary
        spec.replace_var(const_true_var, &[(one.clone(), vec![].into())]);

        if add_children {
            ctx[gate].for_each_child(|&e| {
                // reduce the use by one
                let prev_uses = uses[e];
                assert!(prev_uses > 0);
                uses[e] = prev_uses - 1;
                // did the use count just go down to zero?
                if prev_uses == 1 && is_gate(&ctx[e]) {
                    todo.push((expr_to_var(e), e));
                }
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

fn poly_for_bv_expr(ctx: &mut Context, e: ExprRef) -> Poly {
    let width = e
        .get_bv_type(ctx)
        .expect("function only works with bitvector expressions.");
    let m = polysub::Mod::from_bits(width);
    polysub::Polynom::from_monoms(
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

fn poly_for_bv_literal(value: BitVecValueRef) -> Poly {
    let m = polysub::Mod::from_bits(value.width());
    // we need to convert the value into a coefficient
    let big_value = value.to_big_int();
    let coef = Coef::from_big(&big_value, m);
    // now we create a polynomial with just this coefficient
    let monom = (coef, vec![].into());
    polysub::Polynom::from_monoms(m, vec![monom].into_iter())
}

fn build_bottom_up_poly(ctx: &mut Context, e: ExprRef) -> Poly {
    let poly: Poly = traversal::bottom_up_mut(ctx, e, |ctx, e, children: &[Poly]| {
        match (ctx[e].clone(), children) {
            (Expr::BVSymbol { .. }, _) => poly_for_bv_expr(ctx, e),
            (Expr::BVLiteral(value), _) => poly_for_bv_literal(value.get(ctx)),
            (Expr::BVConcat(_, _, w), [a, b]) => {
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
                r
            }
            (Expr::BVZeroExt { by, .. }, [e]) => {
                let result_width = e.get_mod().bits() + by;
                let new_m = polysub::Mod::from_bits(result_width);
                let mut r: Poly = e.clone();
                r.change_mod(new_m);
                r
            }
            (Expr::BVAdd(ae, be, w), [a, b]) => {
                debug_assert_eq!(w, a.get_mod().bits());
                debug_assert_eq!(w, b.get_mod().bits());
                let mut r = a.clone();
                r.add_assign(b);
                r
            }
            (Expr::BVMul(ae, be, w), [a, b]) => {
                debug_assert_eq!(w, a.get_mod().bits());
                debug_assert_eq!(w, b.get_mod().bits());
                a.mul(b)
            }
            (Expr::BVNegate(_, w), [e]) => {
                todo!()
            }
            (other, cs) => todo!("{other:?}: {cs:?}"),
        }
    });
    poly
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ScaEqualityProblem {
    equality: ExprRef,
    gate_level: ExprRef,
    word_level: ExprRef,
}

pub fn find_sca_simplification_candidates(ctx: &Context, e: ExprRef) -> Vec<ScaEqualityProblem> {
    let mut problems = vec![];
    let _ = traversal::bottom_up(ctx, e, |ctx, e, children: &[AnalysisResult]| {
        // detect equality comparisons of gate and word level expressions
        if let (Expr::BVEqual(ae, be), [a, b]) = (ctx[e].clone(), children) {
            if a.word.is_some() && b.gate.is_some() {
                problems.push(ScaEqualityProblem {
                    equality: e,
                    gate_level: be,
                    word_level: ae,
                });
            }

            if b.word.is_some() && a.gate.is_some() {
                problems.push(ScaEqualityProblem {
                    equality: e,
                    gate_level: ae,
                    word_level: be,
                });
            }
            AnalysisResult::NONE
        } else {
            AnalysisResult::analyze(ctx, e, children)
        }
    });
    problems
}

#[derive(Debug, Clone, PartialEq)]
struct AnalysisResult {
    gate: Option<GateLevelAnalysis>,
    word: Option<WordLevelAnalysis>,
}

impl AnalysisResult {
    const NONE: Self = AnalysisResult {
        gate: None,
        word: None,
    };

    fn analyze(ctx: &Context, e: ExprRef, children: &[Self]) -> AnalysisResult {
        let word = if children.iter().all(|a| a.word.is_some()) {
            let c_word: Vec<_> = children.iter().map(|a| a.word.clone().unwrap()).collect();
            WordLevelAnalysis::analyze(ctx, e, &c_word)
        } else {
            None
        };

        let gate = if children.iter().all(|a| a.gate.is_some()) {
            let c_gate: Vec<_> = children.iter().map(|a| a.gate.clone().unwrap()).collect();
            GateLevelAnalysis::analyze(ctx, e, &c_gate)
        } else {
            None
        };

        Self { word, gate }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct GateLevelAnalysis {}

impl GateLevelAnalysis {
    fn new() -> Self {
        Self {}
    }

    fn analyze(ctx: &Context, e: ExprRef, _children: &[Self]) -> Option<Self> {
        match &ctx[e] {
            // symbols and constants are always OK
            Expr::BVLiteral(_) | Expr::BVSymbol { .. } => Some(Self::new()),
            // extraction in order to get individual bits is expected
            Expr::BVSlice { lo, hi, .. } if lo == hi => Some(Self::new()),
            // single bit gates are ok
            Expr::BVNot(_, w)
            | Expr::BVAnd(_, _, w)
            | Expr::BVOr(_, _, w)
            | Expr::BVXor(_, _, w)
                if *w == 1 =>
            {
                Some(Self::new())
            }

            // concatenation should generally be OK, right?
            Expr::BVConcat(_, _, _) => Some(Self::new()),
            // nothing else
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct WordLevelAnalysis {
    /// the maximum value that the expression can take on
    max_value: BitVecValue,
    /// indicates that there might have been an overflow
    overflow: bool,
}

impl WordLevelAnalysis {
    fn new(max_value: BitVecValue, overflow: bool) -> Self {
        Self {
            max_value,
            overflow,
        }
    }

    fn from_bit_width(w: WidthInt) -> Self {
        let max_value = BitVecValue::ones(w);
        Self::new(max_value, false)
    }

    fn analyze(ctx: &Context, e: ExprRef, children: &[Self]) -> Option<Self> {
        match (ctx[e].clone(), children) {
            (Expr::BVLiteral(value), _) => Some(Self::from_bit_width(value.width())),
            (Expr::BVSymbol { width, .. }, _) => Some(Self::from_bit_width(width)),
            (Expr::BVAdd(_, _, _), [a, b]) => {
                // check for overflow in an add
                let max_value = a.max_value.add(&b.max_value);
                let max_modulo = max_value.zero_extend(1);
                let max_precise = a.max_value.zero_extend(1).add(&b.max_value.zero_extend(1));
                let no_new_overflow = max_modulo.is_equal(&max_precise);
                Some(Self::new(
                    max_value,
                    a.overflow || b.overflow || !no_new_overflow,
                ))
            }
            (Expr::BVMul(_, _, w), [a, b]) => {
                // check for overflow in an mul
                let max_value = a.max_value.mul(&b.max_value);
                let max_modulo = max_value.zero_extend(w);
                let max_precise = a.max_value.zero_extend(w).mul(&b.max_value.zero_extend(w));
                let no_new_overflow = max_modulo.is_equal(&max_precise);
                Some(Self::new(
                    max_value,
                    a.overflow || b.overflow || !no_new_overflow,
                ))
            }
            (Expr::BVNegate(_, _), [_]) => {
                todo!("deal with negate correctly!")
            }
            (Expr::BVZeroExt { by, .. }, [e]) => {
                // todo: forbid normal zero ext and only allow concat version
                if !e.overflow {
                    let max_value = e.max_value.zero_extend(by);
                    Some(Self::new(max_value, false))
                } else {
                    None
                }
            }
            // concat to zero extend is ok
            (Expr::BVConcat(msb, _, _), [a, b]) if ctx.is_zero(msb) => {
                // We can only zero extend if we have not observed a possible overflow, yet.
                // We know that `a` is just a constant zero, so we just need to look at `b`.
                if !b.overflow {
                    let max_value = b.max_value.zero_extend(a.max_value.width());
                    Some(Self::new(max_value, false))
                } else {
                    None
                }
            }
            (_, _) => None, // we are no longer considering this expression a potential word level expression
        }
    }
}

/// Wrapper for pretty printing a polynomial with variable indices replaced by underlying SMT symbol names.
struct PrettyPoly<'a, 'b> {
    ctx: &'a Context,
    poly: &'b Poly,
}

impl<'a, 'b> PrettyPoly<'a, 'b> {
    fn n(ctx: &'a Context, poly: &'b Poly) -> Self {
        Self { ctx, poly }
    }

    fn print_term(&self, f: &mut Formatter<'_>, term: &Term) -> std::fmt::Result {
        for (ii, &v) in term.vars().enumerate() {
            let is_first = ii == 0;
            if !is_first {
                write!(f, " * ")?;
            }
            // turn var index into smt expression and render that
            write!(f, "{}", var_to_expr(v).serialize_to_str(self.ctx))?;
        }
        Ok(())
    }
}

impl<'a, 'b> Display for PrettyPoly<'a, 'b> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.poly.is_zero() {
            write!(f, "0")
        } else {
            let monoms = self.poly.sorted_monom_vec();
            for (ii, (coef, term)) in monoms.iter().enumerate() {
                let is_last = ii == monoms.len() - 1;
                write!(f, "[{coef} * ")?;
                self.print_term(f, term)?;
                write!(f, "]")?;
                if !is_last {
                    write!(f, " + ")?;
                }
            }
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use patronus::expr::{eval_bv_expr, find_symbols};
    use patronus::smt::{BITWUZLA, Logic, SmtCommand, Solver, SolverContext, read_command};
    use rustc_hash::FxHashMap;
    use std::io::BufReader;

    fn read_first_assert_expr(
        ctx: &mut Context,
        filename: impl AsRef<std::path::Path>,
    ) -> Option<ExprRef> {
        // open input file
        let file = std::fs::File::open(filename).expect("failed to open input file");
        let mut reader = BufReader::new(file);
        let mut st = FxHashMap::default();
        while let Some(cmd) =
            read_command(&mut reader, ctx, &mut st).expect("failed to read command")
        {
            if let SmtCommand::Assert(e) = cmd {
                return Some(e);
            }
        }
        None
    }

    fn simplify_coward_smt(filename: &str) {
        let mut ctx = Context::default();
        let e = read_first_assert_expr(&mut ctx, filename).unwrap();
        let candidates = find_sca_simplification_candidates(&ctx, e);
        for p in candidates {
            let sca_based = simplify_word_level_equality(&mut ctx, p).unwrap();
            assert_eq!(sca_based, ctx.get_true());
        }
    }

    const ALL_FILES: &[&str] = &[
        "../inputs/coward/add_three.4_bit.smt2",
        "../inputs/coward/blend.4_bit.smt2",
        "../inputs/coward/dot_product.4_bit.smt2",
        "../inputs/coward/fma.4_bit.smt2",
        "../inputs/coward/fmaa.4_bit.smt2",
        // this file contains several (in) equalities, and thus we need to be smarter in finding them
        "../inputs/coward/fma_share.4_bit.smt2",
    ];

    /// Not really a test, just a way to see some reference polynomials while we are still developing
    #[test]
    fn calculate_reference_polynomials() {
        for filename in ALL_FILES.iter() {
            let mut ctx = Context::default();
            let e = read_first_assert_expr(&mut ctx, filename).unwrap();
            let cs = find_sca_simplification_candidates(&ctx, e);
            for c in cs {
                let word_poly = build_bottom_up_poly(&mut ctx, c.word_level);
                println!("{filename}:\n{}\n", PrettyPoly::n(&ctx, &word_poly));
            }
        }
    }

    /// Performs an exhaustive check of all input values
    fn is_eq_exhaustive(ctx: &Context, p: ScaEqualityProblem) -> bool {
        let word_symbols = find_symbols(ctx, p.word_level);
        let gate_symbols = find_symbols(ctx, p.word_level);
        debug_assert_eq!(word_symbols, gate_symbols);
        let inputs: Vec<_> = word_symbols
            .iter()
            .map(|&s| {
                let width = s.get_bv_type(ctx).unwrap();
                debug_assert!(width <= 16);
                let max_value = (1u64 << width) - 1;
                (
                    ctx[s].get_symbol_name(ctx).unwrap().to_string(),
                    s,
                    width,
                    max_value,
                )
            })
            .collect();

        let mut values = vec![0u64; inputs.len()];
        let max_values: Vec<_> = inputs.iter().map(|(_, _, _, v)| *v).collect();

        let mut count = 0;
        while values != max_values {
            count += 1;
            // perform check
            let symbols: Vec<_> = inputs
                .iter()
                .zip(values.iter())
                .map(|((_, s, w, _), v)| (*s, BitVecValue::from_u64(*v, *w)))
                .collect();

            let word_value = eval_bv_expr(&ctx, symbols.as_slice(), p.word_level);
            let gate_value = eval_bv_expr(&ctx, symbols.as_slice(), p.gate_level);
            let is_equal = eval_bv_expr(&ctx, symbols.as_slice(), p.equality);

            if !is_equal.is_true() || !word_value.is_equal(&gate_value) {
                let syms: Vec<_> = inputs
                    .iter()
                    .zip(values.iter())
                    .map(|((n, _, _, _), v)| format!("{n}={v}"))
                    .collect();
                println!(
                    "Not equal! GATE: {} =/= WORD: {} w/ {}",
                    gate_value.to_dec_str(),
                    word_value.to_dec_str(),
                    syms.join(", ")
                );
                return false;
            }

            // increment
            for (value, max_value) in values.iter_mut().zip(max_values.iter()) {
                debug_assert!(*value <= *max_value);
                if *value == *max_value {
                    *value = 0;
                    // set to zero and go to next "digit"
                } else {
                    *value += 1;
                    break; // done
                }
            }
        }
        println!("expressions appear to be equivalent after {count} iterations");
        true
    }

    #[test]
    fn test_full_adder() {
        let mut ctx = Context::default();
        // out specification
        let a0 = ctx.bv_symbol("a0", 1);
        let b0 = ctx.bv_symbol("b0", 1);
        let c = ctx.bv_symbol("c", 1);
        let word_level = ctx.build(|b| {
            b.add(
                b.add(b.zero_extend(a0, 1), b.zero_extend(b0, 1)),
                b.zero_extend(c, 1),
            )
        });

        // similar to Fig. 1 in FMCAD'22 Divider Verification
        let h1 = ctx.xor(a0, b0);
        let h2 = ctx.and(a0, b0);
        let h3 = ctx.and(c, h1);
        let s0 = ctx.xor(c, h1);
        let c0 = ctx.or(h3, h2);
        let gate_level = ctx.concat(c0, s0);
        let equality = ctx.equal(word_level, gate_level);

        let problem = find_sca_simplification_candidates(&ctx, equality)[0];

        // manually check that our problem is actually correct
        assert!(is_eq_exhaustive(&ctx, problem));

        let result = simplify_word_level_equality(&mut ctx, problem).unwrap();
        assert_eq!(result, ctx.get_true());
    }

    #[test]
    fn test_simple_2bit_adder() {
        let mut ctx = Context::default();
        let a = ctx.bv_symbol("a", 2);
        let b = ctx.bv_symbol("b", 2);
        let word_level = ctx.add(a, b);
        let a_0 = ctx.slice(a, 0, 0);
        let a_1 = ctx.slice(a, 1, 1);
        let b_0 = ctx.slice(b, 0, 0);
        let b_1 = ctx.slice(b, 1, 1);
        let gate_level_0 = ctx.xor(a_0, b_0);
        let carry_1 = ctx.and(a_0, b_0);
        let gate_level_1 = ctx.xor3(a_1, b_1, carry_1);
        let gate_level = ctx.concat(gate_level_1, gate_level_0);
        let equality = ctx.equal(word_level, gate_level);

        let problem = find_sca_simplification_candidates(&ctx, equality)[0];

        // manually check that our problem is actually correct
        assert!(is_eq_exhaustive(&ctx, problem));

        let result = simplify_word_level_equality(&mut ctx, problem).unwrap();
        assert_eq!(result, ctx.get_true());
    }

    #[test]
    fn test_simplify_coward_three_add_2bit() {
        simplify_coward_smt("../inputs/coward/add_three.2_bit.smt2");
    }

    #[test]
    fn test_simplify_coward_three_add() {
        simplify_coward_smt("../inputs/coward/add_three.4_bit.smt2");
    }

    #[test]
    fn test_simplify_coward_blend() {
        simplify_coward_smt("../inputs/coward/blend.4_bit.smt2");
    }

    #[test]
    fn test_simplify_coward_dot_product() {
        simplify_coward_smt("../inputs/coward/dot_product.4_bit.smt2");
    }

    #[test]
    fn test_simplify_coward_fma() {
        simplify_coward_smt("../inputs/coward/fma.4_bit.smt2");
    }

    #[ignore] // currently times out
    #[test]
    fn test_simplify_coward_fmaa() {
        simplify_coward_smt("../inputs/coward/fmaa.4_bit.smt2");
    }

    #[test]
    fn test_simplify_coward_fma_share() {
        simplify_coward_smt("../inputs/coward/fma_share.4_bit.smt2");
    }
}
