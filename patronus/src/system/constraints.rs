// Copyright 2026 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::{Context, Expr, ExprRef, SerializableIrNode, TypeCheck, as_equality};
use crate::system::TransitionSystem;
use rustc_hash::FxHashSet;

/// Turns simple constraints into hardware.
pub fn remove_simple_constraints(ctx: &mut Context, sys: &mut TransitionSystem) {
    todo!()
}

pub fn split_constraints(ctx: &mut Context, sys: &mut TransitionSystem) {
    let mut split = vec![];
    let num_orig_constraints = sys.constraints.len();
    for constraint_idx in 0..num_orig_constraints {
        debug_assert!(split.is_empty());
        let constraint = sys.constraints[constraint_idx];
        if split_conjunction(ctx, constraint, &mut split).is_none() {
            debug_assert!(split.len() > 1);
            // fix names
            if let Some(name_id) = sys.names[constraint] {
                let base = ctx[name_id].clone();
                for (idx, &new_constr) in split.iter().enumerate() {
                    if sys.names[new_constr].is_none() {
                        sys.names[new_constr] = Some(ctx.string(format!("{base}_{idx}").into()));
                    }
                }
            }

            // create new constraints
            sys.constraints[constraint_idx] = split.pop().unwrap();
            sys.constraints.append(&mut split);
        }
    }
}

fn split_conjunction(ctx: &Context, e: ExprRef, out: &mut Vec<ExprRef>) -> Option<ExprRef> {
    match ctx[e].clone() {
        Expr::BVAnd(a, b, _) => {
            if let Some(a) = split_conjunction(ctx, a, out) {
                out.push(a);
            }
            if let Some(b) = split_conjunction(ctx, b, out) {
                out.push(b);
            }
            None
        }
        _ => Some(e),
    }
}

#[derive(Debug, Clone)]
struct InputEq {
    guard: ExprRef,
    input: ExprRef,
    rhs: ExprRef,
}

impl InputEq {
    fn with_guard(mut self, ctx: &mut Context, extra_guard: ExprRef) -> Self {
        self.guard = if ctx[self.guard].is_true() {
            extra_guard
        } else {
            ctx.and(self.guard, extra_guard)
        };
        self
    }
}

fn collect_input_equality_constraints(
    ctx: &mut Context,
    sys: &mut TransitionSystem,
) -> Vec<InputEq> {
    let inps = FxHashSet::from_iter(sys.inputs.iter().cloned());
    let mut consts = vec![];

    for constraint in std::mem::take(&mut sys.constraints) {
        if let Some(c) = is_input_equality(ctx, constraint, &inps) {
            consts.push(c);
        } else {
            debug_assert_eq!(constraint.get_bv_type(ctx), Some(1));
            // check for guarded input equality
            match ctx[constraint].clone() {
                Expr::BVNot(e, ..) if let Expr::BVAnd(x, y, ..) = ctx[e].clone() => {
                    // !(x && y) <=> x => !y <=> y => !x
                    if let Some(c) = is_input_equality(ctx, x, &inps) {
                        consts.push(c.with_guard(ctx, y));
                    } else if let Some(c) = is_input_equality(ctx, y, &inps) {
                        consts.push(c.with_guard(ctx, x));
                    } else {
                        sys.constraints.push(constraint);
                    }
                }
                Expr::BVOr(a, b, ..) => {
                    // (a || b) <=> !a => b <=> !b => a
                    if let Some(c) = is_input_equality(ctx, a, &inps) {
                        let g = ctx.not(b);
                        consts.push(c.with_guard(ctx, g));
                    } else if let Some(c) = is_input_equality(ctx, b, &inps) {
                        let g = ctx.not(a);
                        consts.push(c.with_guard(ctx, g));
                    } else {
                        sys.constraints.push(constraint);
                    }
                }
                _ => {
                    sys.constraints.push(constraint);
                }
            }
        }
    }

    consts
}

fn is_input_equality(ctx: &Context, e: ExprRef, inps: &FxHashSet<ExprRef>) -> Option<InputEq> {
    as_equality(ctx, e)
        .filter(|(s, _)| inps.contains(s))
        .map(|(input, rhs)| InputEq {
            guard: ctx.get_true(),
            input,
            rhs,
        })
}

/// Removes any exact duplicate constraints / bad states without changing the order.
pub fn dedup_constraints_and_bads(sys: &mut TransitionSystem) {
    let mut map = FxHashSet::default();
    sys.constraints.retain(|e| map.insert(*e));
    map.clear();
    sys.bad_states.retain(|e| map.insert(*e));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::btor2::parse_file;
    use crate::expr::SerializableIrNode;
    use crate::system::transform::simplify_expressions;

    #[test]
    fn test_mann_fifo() {
        let (mut ctx, mut sys) =
            parse_file("../inputs/hwmcc/shift_register_top_w64_d16_e0.btor2").unwrap();
        assert_eq!(sys.constraints.len(), 5);
        // recognition only works on a simplified system
        simplify_expressions(&mut ctx, &mut sys);
        let simplified = sys.serialize_to_str(&ctx);
        split_constraints(&mut ctx, &mut sys);
        assert_eq!(
            simplified,
            sys.serialize_to_str(&ctx),
            "in this particular system, there is nothing to split"
        );
        assert_eq!(sys.constraints.len(), 5);
        dedup_constraints_and_bads(&mut sys);
        assert_eq!(sys.constraints.len(), 3);
        let cs = collect_input_equality_constraints(&mut ctx, &mut sys);
        assert!(
            sys.constraints.is_empty(),
            "All three constraints are input equality constraints."
        );
        for c in cs {
            println!(
                "{} == {} when {}",
                c.input.serialize_to_str(&ctx),
                c.rhs.serialize_to_str(&ctx),
                c.guard.serialize_to_str(&ctx)
            )
        }
    }

    #[test]
    fn test_chisel_constraints() {
        let (mut ctx, mut sys) =
            parse_file("../inputs/chiseltest/formal_backend_should_do_division_and_remainder_correctly_for_all_2bit_UInts_DivisionAndRemainderTest.btor").unwrap();
        assert_eq!(sys.constraints.len(), 1);
        simplify_expressions(&mut ctx, &mut sys);
        assert_eq!(sys.constraints.len(), 1);
        split_constraints(&mut ctx, &mut sys);
        assert_eq!(sys.constraints.len(), 1);
        println!("{}", sys.serialize_to_str(&ctx));
        let cs = collect_input_equality_constraints(&mut ctx, &mut sys);
        assert!(
            sys.constraints.is_empty(),
            // TODO: should we remove BVImplies in the simplifier or add another pattern here?
            "TODO: deal with implies constraint!"
        );
        for c in cs {
            println!(
                "{} == {} when {}",
                c.input.serialize_to_str(&ctx),
                c.rhs.serialize_to_str(&ctx),
                c.guard.serialize_to_str(&ctx)
            )
        }
    }
}
