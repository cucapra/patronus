// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
/*!
# Arithmetic Rewrite Rules

We use our own custom struct to define rewrite rules. This allows us to
introspect them in order to check re-write conditions or debug matches.

!*/

use crate::arithmetic::{eval_width_left_shift, eval_width_max_plus_1};
use crate::{Arith, EGraph, WidthConstantFold, get_const_width_or_sign, is_bin_op};
use egg::{
    ConditionalApplier, ENodeOrVar, Id, Language, Pattern, PatternAst, Searcher, Subst, Var,
};
use patronus::expr::WidthInt;
use std::cmp::max;

/// our version of the egg re-write macro
macro_rules! arith_rewrite {
    (
        $name:expr;
        $lhs:expr => $rhs:expr
    ) => {{ ArithRewrite::new::<&str>($name, $lhs, $rhs, [], None) }};
    (
        $name:expr;
        $lhs:expr => $rhs:expr;
        if $vars:expr, $cond:expr
    ) => {{ ArithRewrite::new($name, $lhs, $rhs, $vars, Some($cond)) }};
}

/// Generate our ROVER inspired rewrite rules.
pub fn create_rewrites() -> Vec<ArithRewrite> {
    vec![
        // a + b => b + a
        arith_rewrite!("commute-add"; "(+ ?wo ?wa ?sa ?a ?wb ?sb ?b)" => "(+ ?wo ?wb ?sb ?b ?wa ?sa ?a)"),
        // a * b => b * a
        arith_rewrite!("commute-mul"; "(* ?wo ?wa ?sa ?a ?wb ?sb ?b)" => "(* ?wo ?wb ?sb ?b ?wa ?sa ?a)"),
        // (a << b) << x => a << (b + c)
        arith_rewrite!("merge-left-shift";
            // we require that b, c and (b + c) are all unsigned
            // we do not want (b + c) to wrap, because in that case the result would always be zero
            // the value being shifted has to be consistently signed or unsigned
            "(<< ?wo ?wab ?sa (<< ?wab ?wa ?sa ?a ?wb unsign ?b) ?wc unsign ?c)" =>
            "(<< ?wo ?wa ?sa ?a (max+1 ?wb ?wc) unsign (+ (max+1 ?wb ?wc) ?wb unsign ?b ?wc unsign ?c))";
            // wab >= wo
            if["?wo", "?wab"], |w| w[1] >= w[0]),
        // a << (b + c) => (a << b) << x
        arith_rewrite!("unmerge-left-shift";
            // we require that b, c and (b + c) are all unsigned
            // we do not want (b + c) to wrap, because in that case the result would always be zero
            // the value being shifted has to be consistently signed or unsigned
            "(<< ?wo ?wa ?sa ?a ?wbc unsign (+ ?wbc ?wb unsign ?b ?wc unsign ?c))" =>
            // RHS: we set wab to the minimum not to overflow
            "(<< ?wo (wlsh ?wa ?wb) ?sa (<< (wlsh ?wa ?wb) ?wa ?sa ?a ?wb unsign ?b) ?wc unsign ?c)";
            // ?wbc >= max(wb, wc) + 1
            if["?wbc", "?wb", "?wc"], |w| w[0] >= (max(w[1], w[2]) + 1)),
        // a * 2 <=> a + a
        arith_rewrite!("mult-to-add";
            "(* ?wo ?wa ?sa ?a ?wb ?sb 2)" =>
            "(+ ?wo ?wa ?sa ?a ?wa ?sa ?a)";
            // (!sb && wb > 1) || (sb && wb > 2) || (wo <= wb)
           if["?wb", "?sb", "?wo"],
            |w| (w[1] == 0 && w[0] > 1) || (w[1] == 1 && w[0] > 2) || w[2] <= w[0]),
        // (a * b) << c => (a << c) * b
        arith_rewrite!("left-shift-mult";
            // TODO: currently all signs are forced to unsigned
            "(<< ?wo ?wab unsign (* ?wab ?wa unsign ?a ?wb unsign ?b) ?wc unsign ?c)" =>
            // RHS: we set wac to the minimum not to overflow
            "(* ?wo (wlsh ?wa ?wc) unsign (<< (wlsh ?wa ?wc) ?wa unsign ?a ?wc unsign ?c) ?wb unsign ?b)";
            // we want to determine that there is no overflow
            // lhs: wab >= wa + wb && wo >= wab + max_shift(wc)
            // rhs: wac >= wa + max_shift(c) && wo >= wac + wb
            if["?wab", "?wa", "?wb", "?wo", "?wc"], |w| mul_no_ov(w[0], w[1], w[2]) && lsh_no_ov(w[3], w[0], w[4])),
    ]
}

/// Determines if there is no overflow possible for this addition.
fn add_no_ov(wo: WidthInt, wa: WidthInt, wb: WidthInt) -> bool {
    wo >= eval_width_max_plus_1(wa, wb)
}

/// Determines if there is no overflow possible for this multiplication.
fn mul_no_ov(wo: WidthInt, wa: WidthInt, wb: WidthInt) -> bool {
    wo >= wa + wb
}

/// Determines if there is no overflow possible for this left shift.
fn lsh_no_ov(wo: WidthInt, wa: WidthInt, wb: WidthInt) -> bool {
    wo >= eval_width_left_shift(wa, wb)
}

pub struct ArithRewrite {
    name: String,
    /// most general lhs pattern
    lhs: Pattern<Arith>,
    /// rhs pattern with all widths derived from the lhs, maybe be the same as rhs
    rhs_derived: Pattern<Arith>,
    /// variables use by the condition
    cond_vars: Vec<Var>,
    /// condition of the re_write
    cond: Option<fn(&[WidthInt]) -> bool>,
}

pub type Rewrite = egg::Rewrite<Arith, WidthConstantFold>;

impl ArithRewrite {
    fn new<S: AsRef<str>>(
        name: &str,
        lhs: &str,
        rhs_derived: &str,
        cond_vars: impl IntoIterator<Item = S>,
        cond: Option<fn(&[WidthInt]) -> bool>,
    ) -> Self {
        let cond_vars = cond_vars
            .into_iter()
            .map(|n| n.as_ref().parse().unwrap())
            .collect();
        let lhs = lhs.parse::<_>().unwrap();
        check_width_consistency(&lhs);
        let rhs_derived = rhs_derived.parse::<_>().unwrap();
        check_width_consistency(&rhs_derived);
        Self {
            name: name.to_string(),
            lhs,
            rhs_derived,
            cond,
            cond_vars,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn patterns(&self) -> (&PatternAst<Arith>, &PatternAst<Arith>) {
        (&self.lhs.ast, &self.rhs_derived.ast)
    }

    pub fn to_egg(&self) -> Vec<Rewrite> {
        // TODO: support bi-directional rules
        if let Some(cond) = self.cond {
            let vars: Vec<Var> = self.cond_vars.clone();
            let condition = move |egraph: &mut EGraph, _, subst: &Subst| {
                let values: Vec<WidthInt> = vars
                    .iter()
                    .map(|v| {
                        get_const_width_or_sign(egraph, subst[*v])
                            .expect("failed to find constant width")
                    })
                    .collect();
                cond(values.as_slice())
            };
            let cond_app = ConditionalApplier {
                condition,
                applier: self.rhs_derived.clone(),
            };
            vec![Rewrite::new(self.name.clone(), self.lhs.clone(), cond_app).unwrap()]
        } else {
            vec![
                Rewrite::new(
                    self.name.clone(),
                    self.lhs.clone(),
                    self.rhs_derived.clone(),
                )
                .unwrap(),
            ]
        }
    }

    pub fn eval_condition(&self, a: &[(Var, WidthInt)]) -> bool {
        if let Some(cond) = self.cond {
            let values: Vec<WidthInt> = self
                .cond_vars
                .iter()
                .map(|v| a.iter().find(|(k, _)| k == v).unwrap().1)
                .collect();
            cond(values.as_slice())
        } else {
            // unconditional rewrite
            true
        }
    }

    /// Find all matches of the left-hand-side and returns information about them.
    /// This can be very useful when debugging why a certain rules does not match, when you expect
    /// it to match.
    pub fn find_lhs_matches(&self, egraph: &EGraph) -> Vec<ArithMatch> {
        self.lhs
            .search(egraph)
            .into_iter()
            .flat_map(|m| {
                let eclass = m.eclass;
                m.substs.into_iter().map(move |s| {
                    let assign = substitution_to_assignment(egraph, &s, &self.lhs.ast);
                    let cond_res = self.eval_condition(&assign);
                    ArithMatch {
                        eclass,
                        assign,
                        cond_res,
                    }
                })
            })
            .collect()
    }
}

fn substitution_to_assignment(
    egraph: &EGraph,
    s: &Subst,
    pattern: &PatternAst<Arith>,
) -> Assignment {
    vars_in_pattern(pattern)
        .flat_map(|v| get_const_width_or_sign(egraph, s[v]).map(|w| (v, w)))
        .collect()
}

fn vars_in_pattern(pattern: &PatternAst<Arith>) -> impl Iterator<Item = Var> + '_ {
    pattern.as_ref().iter().flat_map(|e| match e {
        ENodeOrVar::Var(v) => Some(*v),
        ENodeOrVar::ENode(_) => None,
    })
}

pub type Assignment = Vec<(Var, WidthInt)>;

#[derive(Debug, Clone)]
pub struct ArithMatch {
    pub eclass: Id,
    pub assign: Assignment,
    pub cond_res: bool,
}

/// Checks that input and output widths of operations are consistent.
fn check_width_consistency(pattern: &Pattern<Arith>) {
    let exprs = pattern.ast.as_ref();
    for e_node_or_var in exprs.iter() {
        if let ENodeOrVar::ENode(expr) = e_node_or_var {
            if is_bin_op(expr) {
                // w, w_a, s_a, a, w_b, s_b, b
                let a_width_id = usize::from(expr.children()[1]);
                let a_id = usize::from(expr.children()[3]);
                if let Some(a_op_out_width_id) = get_output_width_id(&exprs[a_id]) {
                    assert_eq!(
                        a_width_id, a_op_out_width_id,
                        "In `{expr}`, subexpression `{}` has inconsistent width: {} != {}",
                        &exprs[a_id], &exprs[a_width_id], &exprs[a_op_out_width_id]
                    );
                }
                let b_width_id = usize::from(expr.children()[4]);
                let b_id = usize::from(expr.children()[6]);
                if let Some(b_op_out_width_id) = get_output_width_id(&exprs[b_id]) {
                    assert_eq!(
                        b_width_id, b_op_out_width_id,
                        "In `{expr}`, subexpression `{}` has inconsistent width: {} != {}",
                        &exprs[b_id], &exprs[b_width_id], &exprs[b_op_out_width_id]
                    );
                }
            }
        }
    }
}

/// returns the egg id of the output width, if `expr` has one
fn get_output_width_id(expr: &ENodeOrVar<Arith>) -> Option<usize> {
    if let ENodeOrVar::ENode(expr) = expr {
        if is_bin_op(expr) {
            // w, w_a, s_a, a, w_b, s_b, b
            Some(usize::from(expr.children()[0]))
        } else {
            None
        }
    } else {
        None
    }
}

/// returns all our rewrites in a format that can be directly used by egg
pub fn create_egg_rewrites() -> Vec<Rewrite> {
    create_rewrites()
        .into_iter()
        .map(|r| r.to_egg())
        .reduce(|mut a, mut b| {
            a.append(&mut b);
            a
        })
        .unwrap_or(vec![])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::verification_fig_1;
    use crate::to_arith;
    use patronus::expr::{Context, SerializableIrNode};
    #[test]
    fn test_data_path_verification_fig_1_rewrites() {
        let mut ctx = Context::default();
        let (spec, implementation) = verification_fig_1(&mut ctx);
        let spec_e = to_arith(&ctx, spec);
        let impl_e = to_arith(&ctx, implementation);

        // run egraph operations
        let egg_rewrites = create_egg_rewrites();
        let runner = egg::Runner::default()
            .with_expr(&spec_e)
            .with_expr(&impl_e)
            .run(&egg_rewrites);

        let spec_class = runner.egraph.find(runner.roots[0]);
        let impl_class = runner.egraph.find(runner.roots[1]);
        assert_eq!(spec_class, impl_class, "should prove equality!");
    }

    #[allow(dead_code)]
    fn inspect_e_class(egraph: &EGraph, id: usize) -> String {
        let nodes = egraph[id.into()]
            .nodes
            .iter()
            .map(|n| format!("{n} {:?}", n.children()))
            .collect::<Vec<_>>();
        format!("Class {id}: {}", nodes.join(", "))
    }

    #[test]
    fn test_rewrites() {
        let mut ctx = Context::default();
        let a = ctx.bv_symbol("A", 16);
        let b = ctx.bv_symbol("B", 16);
        let in_smt_expr = ctx.add(a, b);
        let in_smt_expr_2 = ctx.add(b, a);
        assert_eq!(in_smt_expr.serialize_to_str(&ctx), "add(A, B)");

        // run egraph operations
        let egg_expr_in = to_arith(&ctx, in_smt_expr);
        let egg_expr_in_2 = to_arith(&ctx, in_smt_expr_2);
        let egg_rewrites = create_egg_rewrites();
        let runner = egg::Runner::default()
            .with_expr(&egg_expr_in)
            .with_expr(&egg_expr_in_2)
            .run(&egg_rewrites);

        let final_eclass_1 = runner.egraph.find(runner.roots[0]);
        let final_eclass_2 = runner.egraph.find(runner.roots[1]);
        assert_eq!(
            final_eclass_1, final_eclass_2,
            "inputs should be equivalent with commute-add"
        );
    }
}
