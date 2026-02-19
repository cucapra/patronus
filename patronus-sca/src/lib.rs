// Copyright 2026 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

mod rewrite;

use crate::rewrite::{backwards_sub, build_gate_polynomial};
use baa::{BitVecOps, BitVecValue, BitVecValueRef};
use patronus::expr::*;
use polysub::{Coef, Term, VarIndex};
use rustc_hash::FxHashSet;
use std::fmt::{Display, Formatter};

#[derive(Debug, Clone, PartialEq)]
pub enum ScaVerifyResult {
    /// Word and gate level were proven to be equivalent for all inputs.
    Equal,
    /// Could not prove or disprove equivalence
    Unknown,
    /// Word and gate level are not equivalent, see provided counter example.
    Unequal(Vec<(ExprRef, BitVecValue)>),
}

/// Returns a new expressions reference if simplification was possible
pub fn verify_word_level_equality(ctx: &mut Context, p: ScaEqualityProblem) -> ScaVerifyResult {
    let width = p.word_level.get_bv_type(ctx).unwrap();
    debug_assert_eq!(width, p.gate_level.get_bv_type(ctx).unwrap());

    // create a reference polynomial from the word level side
    let (mut word_poly, inputs) = match build_bottom_up_poly(ctx, p.word_level) {
        None => return ScaVerifyResult::Unknown,
        Some(p) => p,
    };
    println!("word-level polynomial: {word_poly}");

    // collect all (bit-level) input variables
    let input_vars: FxHashSet<VarIndex> = inputs
        .iter()
        .flat_map(|&e| {
            let width = e.get_bv_type(ctx).unwrap();
            let vars: Vec<_> = (0..width)
                .map(|bit| expr_to_var(extract_bit(ctx, e, bit)))
                .collect();
            vars
        })
        .collect();

    //let gate_poly = build_gate_polynomial(ctx, &input_vars, word_poly.get_mod(), p.gate_level);

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
    let result = backwards_sub(ctx, &input_vars, gate_outputs, p.gate_level, spec);

    if result.is_zero() {
        ScaVerifyResult::Equal
    } else {
        let witness = extract_witness(ctx, &result, inputs.iter().cloned());
        // check witness
        let is_equal = eval_bv_expr(ctx, witness.as_slice(), p.equality);
        if is_equal.is_true() {
            println!(
                "ERROR: the polynomial does not reduce to zero, but we were not able to find a witness to show inequality. Returning Unknown."
            );
            ScaVerifyResult::Unknown
        } else {
            ScaVerifyResult::Unequal(witness)
        }
    }
}

/// Try to extract a witness from a non-zero polynomial by finding the term with the smallest
/// number of variables.
/// TODO: does this always return a true witness??
fn extract_witness(
    ctx: &mut Context,
    p: &Poly,
    inputs: impl Iterator<Item = ExprRef>,
) -> Vec<(ExprRef, BitVecValue)> {
    let monoms = p.sorted_monom_vec();

    // find smallest term
    let mut smallest_size = monoms.first().unwrap().1.var_count();
    let mut smallest_index = 0;
    for (ii, (_, t)) in monoms.iter().enumerate() {
        if smallest_size == 0 {
            break; // early exit if there is a constant term
        }
        if t.var_count() < smallest_size {
            smallest_size = t.var_count();
            smallest_index = ii;
        }
    }

    // we need to set all vars in the smallest term to 1, everything else to zero
    let is_one: FxHashSet<_> = monoms[smallest_index].1.vars().cloned().collect();

    // small sanity check for debugging
    let mut defined_ones = FxHashSet::default();

    let w: Vec<_> = inputs
        .map(|input| {
            let width = input.get_bv_type(ctx).unwrap();
            let mut value = BitVecValue::zero(width);
            for bit in 0..width {
                let bit_expr = extract_bit(ctx, input, bit);
                let bit_var = expr_to_var(bit_expr);
                if is_one.contains(&bit_var) {
                    let one = BitVecValue::from_u64(1, width);
                    let shift_by = BitVecValue::from_u64(bit as u64, width);
                    let mask = one.shift_left(&shift_by);
                    value = value.or(&mask);
                    defined_ones.insert(bit_var);
                }
            }
            (input, value)
        })
        .collect();

    let ones_not_defined: Vec<_> = is_one.difference(&defined_ones).cloned().collect();
    assert!(
        ones_not_defined.is_empty(),
        "Some variables did not map to inputs."
    );
    w
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
/// Used for building the word-level polynomial
type Poly = polysub::Polynom<DefaultCoef>;

fn expr_to_var(e: ExprRef) -> polysub::VarIndex {
    (usize::from(e) as u32).into()
}

fn var_to_expr(v: polysub::VarIndex) -> ExprRef {
    usize::from(v).into()
}

fn poly_for_bv_expr(ctx: &mut Context, e: ExprRef) -> Poly {
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

fn poly_for_bv_literal(value: BitVecValueRef) -> Poly {
    let m = polysub::Mod::from_bits(value.width());
    // we need to convert the value into a coefficient
    let big_value = value.to_big_int();
    let coef = Coef::from_big(&big_value, m);
    // now we create a polynomial with just this coefficient
    let monom = (coef, vec![].into());
    Poly::from_monoms(m, vec![monom].into_iter())
}

/// Returns a polynomial representation of the expression + all input expressions if possible.
/// Returns `None` if the conversion fails.
fn build_bottom_up_poly(ctx: &mut Context, e: ExprRef) -> Option<(Poly, Vec<ExprRef>)> {
    let mut inputs = vec![];
    let (poly, _overflow) =
        traversal::bottom_up_mut(ctx, e, |ctx, e, children: &[Option<(Poly, bool)>]| {
            // have we given up yet?
            if children.iter().any(|c| c.is_none()) {
                return None;
            }

            match (ctx[e].clone(), children) {
                (Expr::BVSymbol { .. }, _) => {
                    inputs.push(e);
                    Some((poly_for_bv_expr(ctx, e), false))
                }
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
        })?;
    inputs.sort();
    inputs.dedup();
    Some((poly, inputs))
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ScaEqualityProblem {
    equality: ExprRef,
    gate_level: ExprRef,
    word_level: ExprRef,
}

impl ScaEqualityProblem {
    pub fn equality_expr(&self) -> ExprRef {
        self.equality
    }

    /// Runs the provided simplifier on the gate-level expression.
    pub fn simplify_gate_level<T: ExprMap<Option<ExprRef>>>(
        &self,
        ctx: &mut Context,
        simplifier: &mut Simplifier<T>,
    ) -> Self {
        let mut r = self.clone();
        r.gate_level = simplifier.simplify(ctx, self.gate_level);
        r
    }
}

pub fn find_sca_simplification_candidates(ctx: &Context, e: ExprRef) -> Vec<ScaEqualityProblem> {
    let mut problems = vec![];
    let _ = traversal::bottom_up(ctx, e, |ctx, e, children: &[AnalysisResult]| {
        // detect equality comparisons of gate and word level expressions
        if let (Expr::BVEqual(ae, be), [a, b]) = (ctx[e].clone(), children) {
            if a.word && b.gate {
                problems.push(ScaEqualityProblem {
                    equality: e,
                    gate_level: be,
                    word_level: ae,
                });
            }

            if b.word && a.gate {
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
    /// if true, then the expression may be a valid gate-level expression
    gate: bool,
    /// if true, then the expression may be a valid word-level expression
    word: bool,
}

impl AnalysisResult {
    const NONE: Self = AnalysisResult {
        gate: false,
        word: false,
    };

    fn analyze(ctx: &Context, e: ExprRef, children: &[Self]) -> AnalysisResult {
        let word = if children.iter().all(|a| a.word) {
            is_word_level_expr(ctx, e)
        } else {
            false
        };

        let gate = if children.iter().all(|a| a.gate) {
            is_gate_level_expr(ctx, e)
        } else {
            false
        };

        Self { word, gate }
    }
}

/// Returns `true` if the expression may be part of a word-level expression.
fn is_word_level_expr(ctx: &Context, e: ExprRef) -> bool {
    let simple_expr = matches!(
        &ctx[e],
        Expr::BVLiteral(_)
            | Expr::BVSymbol { .. }
            | Expr::BVAdd(_, _, _)
            | Expr::BVMul(_, _, _)
            | Expr::BVNegate(_, _)
            | Expr::BVZeroExt { .. }
    );
    let zero_ext_concat = matches!(&ctx[e], Expr::BVConcat(msb, _, _) if ctx.is_zero(*msb));
    simple_expr || zero_ext_concat
}

/// Returns `true` if the expression may be part of a gate-level expression.
fn is_gate_level_expr(ctx: &Context, e: ExprRef) -> bool {
    let simple_expr = matches!(
        &ctx[e],
        // symbols and constants are always OK
        Expr::BVLiteral(_) | Expr::BVSymbol { .. } |
            // concatenation should generally be OK, right?
            Expr::BVConcat(_, _, _)
    );
    let one_bit_gate = matches!(&ctx[e],  Expr::BVNot(_, w)
            | Expr::BVAnd(_, _, w)
            | Expr::BVOr(_, _, w)
            | Expr::BVXor(_, _, w)
                if *w == 1 );
    let one_bit_slice = matches!(&ctx[e],  Expr::BVSlice { lo, hi, .. } if lo == hi);
    simple_expr || one_bit_gate || one_bit_slice
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
    use patronus::smt::{BITWUZLA, SmtCommand, Solver, read_command};
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

    fn check_eq_coward_smt(filename: &str) {
        let mut ctx = Context::default();
        let e = read_first_assert_expr(&mut ctx, filename).unwrap();
        let candidates = find_sca_simplification_candidates(&ctx, e);
        let mut simpl = Simplifier::new(DenseExprMetaData::default());
        for p in candidates {
            println!("GATE: {}", p.gate_level.serialize_to_str(&ctx));
            let p = p.simplify_gate_level(&mut ctx, &mut simpl);
            println!("OPT-GATE: {}", p.gate_level.serialize_to_str(&ctx));
            let sca_based = verify_word_level_equality(&mut ctx, p);
            assert_eq!(sca_based, ScaVerifyResult::Equal);
        }
        let mut solver = BITWUZLA.start(None).unwrap();
        simpl.verify_simplification(&mut ctx, &mut solver).unwrap();
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
                if let Some((word_poly, _inputs)) = build_bottom_up_poly(&mut ctx, c.word_level) {
                    println!("{filename}:\n{}\n", PrettyPoly::n(&ctx, &word_poly));
                } else {
                    println!(
                        "{filename}:\nFailed to build polynom from {}\n",
                        c.word_level.serialize_to_str(&ctx)
                    );
                }
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

        let result = verify_word_level_equality(&mut ctx, problem);
        assert_eq!(result, ScaVerifyResult::Equal);
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

        let result = verify_word_level_equality(&mut ctx, problem);
        assert_eq!(result, ScaVerifyResult::Equal);
    }

    #[test]
    fn test_incorrect_2bit_adder() {
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
        let gate_level_1 = ctx.majority(a_1, b_1, carry_1);
        let gate_level = ctx.concat(gate_level_1, gate_level_0);
        let equality = ctx.equal(word_level, gate_level);

        let problem = find_sca_simplification_candidates(&ctx, equality)[0];

        // manually check that our problem is actually incorrect
        assert!(!is_eq_exhaustive(&ctx, problem));

        let result = verify_word_level_equality(&mut ctx, problem);
        if let ScaVerifyResult::Unequal(w) = result {
            println!("Witness: {w:?}");
        } else {
            unreachable!("{result:?}");
        }
    }

    #[test]
    fn test_simplify_coward_three_add_2bit() {
        check_eq_coward_smt("../inputs/coward/add_three.2_bit.smt2");
    }

    #[test]
    fn test_simplify_coward_three_add() {
        check_eq_coward_smt("../inputs/coward/add_three.4_bit.smt2");
    }

    #[test]
    fn test_simplify_coward_blend() {
        check_eq_coward_smt("../inputs/coward/blend.4_bit.smt2");
    }

    #[test]
    fn test_simplify_coward_dot_product() {
        check_eq_coward_smt("../inputs/coward/dot_product.4_bit.smt2");
    }

    #[test]
    fn test_simplify_coward_fma() {
        check_eq_coward_smt("../inputs/coward/fma.4_bit.smt2");
    }

    #[ignore] // currently times out
    #[test]
    fn test_simplify_coward_fmaa() {
        check_eq_coward_smt("../inputs/coward/fmaa.4_bit.smt2");
    }

    #[test]
    fn test_simplify_coward_fma_share() {
        check_eq_coward_smt("../inputs/coward/fma_share.4_bit.smt2");
    }
}
