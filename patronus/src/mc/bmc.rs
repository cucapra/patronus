// Copyright 2023 The Regents of the University of California
// Copyright 2024-2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::*;
use crate::mc::Witness;
use crate::mc::encoding::{TransitionSystemEncoding, UnrollSmtEncoding};
use crate::mc::types::{InitValue, ModelCheckResult, Result};
use crate::mc::utils::{check_assuming, check_assuming_end, get_smt_value};
use crate::smt::*;
use crate::system::TransitionSystem;
use crate::system::analysis::count_system_expr_uses;
use baa::*;

/// Runs up to [k_max] steps of BMC.
///
/// * [check_constraints] perform additional checking to ensure that
///   the assumptions are satisfiable.
/// * [check_bad_states_individually] perform one SMT solver check per assertion instead of
///   combining them into a single check.
pub fn bmc(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
    check_constraints: bool,
    check_bad_states_individually: bool,
    k_max: u64,
) -> Result<ModelCheckResult> {
    assert!(k_max > 0 && k_max <= 2000, "unreasonable k_max={}", k_max);

    let mut enc = match start_bmc_or_pdr(ctx, smt_ctx, sys)? {
        (r, None) => return Ok(r),
        (_, Some(enc)) => enc,
    };
    enc.init_at(ctx, smt_ctx, 0)?;

    let constraints = sys.constraints.clone();
    let bad_states = sys.bad_states.clone();

    if k_max > 0 && sys.states.is_empty() {
        println!(
            "[warn]: k_max={k_max} is unnecessarily large. System {} has no states.",
            sys.name
        );
    }

    for k in 0..=k_max {
        // assume all constraints hold in this step
        for expr_ref in constraints.iter() {
            let expr = enc.expr_at_step(ctx, *expr_ref, k);
            smt_ctx.assert(ctx, expr)?;
        }

        // make sure the constraints are not contradictory
        if check_constraints {
            let res = smt_ctx.check_sat()?;
            assert_eq!(
                res,
                CheckSatResponse::Sat,
                "Found unsatisfiable constraints in cycle {}",
                k
            );
        }

        if check_bad_states_individually {
            for expr_ref in bad_states.iter() {
                let expr = enc.expr_at_step(ctx, *expr_ref, k);
                let res = check_assuming(ctx, smt_ctx, [expr])?;

                // count expression uses
                let use_counts = count_system_expr_uses(ctx, sys);
                if res == CheckSatResponse::Sat {
                    let wit = get_witness(sys, ctx, &use_counts, smt_ctx, &enc, k, &bad_states)?;
                    return Ok(ModelCheckResult::Fail(wit));
                }
                check_assuming_end(smt_ctx)?;
            }
        } else {
            let all_bads = bad_states
                .iter()
                .map(|expr_ref| enc.expr_at_step(ctx, *expr_ref, k))
                .collect::<Vec<_>>();
            let any_bad = all_bads.into_iter().reduce(|a, b| ctx.or(a, b)).unwrap();
            let res = check_assuming(ctx, smt_ctx, [any_bad])?;

            // count expression uses
            let use_counts = count_system_expr_uses(ctx, sys);
            if res == CheckSatResponse::Sat {
                let wit = get_witness(sys, ctx, &use_counts, smt_ctx, &enc, k, &bad_states)?;
                return Ok(ModelCheckResult::Fail(wit));
            }
            check_assuming_end(smt_ctx)?;
        }

        // advance
        enc.unroll(ctx, smt_ctx)?;
    }

    // we have not found any assertion violations
    Ok(ModelCheckResult::Success)
}

pub(crate) fn start_bmc_or_pdr<S: SolverContext>(
    ctx: &mut Context,
    smt_ctx: &mut S,
    sys: &TransitionSystem,
) -> Result<(
    ModelCheckResult,
    Option<impl TransitionSystemEncoding + use<S>>,
)> {
    // if there are no assertions, there cannot be an error!
    if sys.bad_states.is_empty() {
        return Ok((ModelCheckResult::Success, None));
    }

    // z3 only supports the non-standard as-const array syntax when the logic is set to ALL
    let logic = if smt_ctx.name() == "z3" {
        Logic::All
    } else if smt_ctx.supports_uf() {
        Logic::QfAufbv
    } else {
        Logic::QfAbv
    };
    smt_ctx.set_logic(logic)?;

    // TODO: maybe add support for the more compact SMT encoding
    let enc = UnrollSmtEncoding::new(ctx, sys, false);
    enc.define_header(smt_ctx)?;

    Ok((ModelCheckResult::Unknown, Some(enc)))
}

#[allow(clippy::too_many_arguments)]
fn get_witness(
    sys: &TransitionSystem,
    ctx: &mut Context,
    _use_counts: &[UseCountInt], // TODO: analyze array expressions in order to record which indices are accessed
    smt_ctx: &mut impl SolverContext,
    enc: &impl TransitionSystemEncoding,
    k_max: u64,
    bad_states: &[ExprRef],
) -> Result<Witness> {
    let mut wit = Witness::default();

    // which bad states did we hit?
    for (bad_idx, expr) in bad_states.iter().enumerate() {
        let sym_at = enc.expr_at_step(ctx, *expr, k_max);
        let value = get_smt_value(ctx, smt_ctx, sym_at)?;
        let value = match value {
            Value::Array(_) => unreachable!("should always be a bitvector!"),
            Value::BitVec(v) => v,
        };
        if !value.is_zero() {
            // was the bad state condition fulfilled?
            wit.failed_safety.push(bad_idx as u32);
        }
    }

    // collect initial values
    for (state_cnt, state) in sys.states.iter().enumerate() {
        let sym_at = enc.expr_at_step(ctx, state.symbol, 0);
        let value = get_smt_value(ctx, smt_ctx, sym_at)?;
        // we assume that state ids are monotonically increasing with +1
        assert_eq!(wit.init.len(), state_cnt);
        // convert to a witness value
        let wit_value = match value {
            Value::Array(v) => {
                // TODO: narrow down the relevant indices
                let indices = (0..v.num_elements())
                    .map(|ii| BitVecValue::from_u64(ii as u64, v.index_width()))
                    .collect::<Vec<_>>();
                InitValue::Array(v, indices)
            }
            Value::BitVec(v) => InitValue::BitVec(v),
        };
        wit.init.push(wit_value);
        // also save state name
        wit.init_names
            .push(Some(ctx.get_symbol_name(state.symbol).unwrap().to_string()))
    }

    // save input names
    for input in sys.inputs.iter() {
        wit.input_names
            .push(Some(ctx.get_symbol_name(*input).unwrap().to_string()));
    }

    for k in 0..=k_max {
        let mut input_values = Vec::default();
        for input in sys.inputs.iter() {
            let sym_at = enc.expr_at_step(ctx, *input, k);
            let value = get_smt_value(ctx, smt_ctx, sym_at)?;
            input_values.push(Some(value));
        }
        wit.inputs.push(input_values);
    }

    Ok(wit)
}
