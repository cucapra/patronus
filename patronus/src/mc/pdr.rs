// Copyright 2024-2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::*;
use crate::mc::bmc::start_bmc_or_pdr;
use crate::mc::{
    ModelCheckResult, TransitionSystemEncoding, UnrollSmtEncoding, check_assuming,
    check_assuming_end,
};
use crate::smt::*;
use crate::system::TransitionSystem;

/// Runs PDR
/// Initial implementation was inspired by the IC3 bits implementation in the pono model checker
/// from Stanford.
pub fn pdr(
    ctx: &mut Context,
    smt: &mut impl SolverContext,
    sys: &TransitionSystem,
) -> Result<ModelCheckResult> {
    let mut enc = match start_bmc_or_pdr(ctx, smt, sys)? {
        (r, None) => return Ok(r),
        (_, Some(enc)) => enc,
    };

    assert!(!sys.states.is_empty());

    // we create a representation of the initial state @ time 0
    let init_step = enc.init_at(ctx, smt, 0)?;

    // we create a step between two states that are not related to init
    let s0 = enc.unroll_no_constraints(ctx, smt)?;
    let s1 = enc.unroll(ctx, smt)?;

    let mut state = Pdr::default();

    // initial frame R_0 implies I
    state.push_frame(ctx, smt)?;
    let s0_is_init = state_equality(ctx, sys, &mut enc, init_step, s0);
    let implies_init = ctx.implies(state.frames[0].label, s0_is_init);
    smt.assert(ctx, implies_init)?;
    let init_label = state.frames[0].label;

    // check to see if property violated in initial state
    let any_bad_init = any_bad_at(ctx, sys, &mut enc, init_step);
    match check_assuming(ctx, smt, [any_bad_init])? {
        CheckSatResponse::Sat => {
            todo!("generate a witness and return a failure!")
        }
        CheckSatResponse::Unsat => {}
        CheckSatResponse::Unknown => {}
    }
    check_assuming_end(smt)?;

    // step 1
    state.push_frame(ctx, smt)?;
    let any_bad_s1 = any_bad_at(ctx, sys, &mut enc, s1);
    match check_assuming(ctx, smt, [init_label, any_bad_s1])? {
        CheckSatResponse::Sat => {
            todo!("generate a witness and return a failure!")
        }
        CheckSatResponse::Unsat => {}
        CheckSatResponse::Unknown => {}
    }
    check_assuming_end(smt)?;

    // next steps

    Ok(ModelCheckResult::Unknown)
}

fn any_bad_at(
    ctx: &mut Context,
    sys: &TransitionSystem,
    enc: &mut impl TransitionSystemEncoding,
    step: u64,
) -> ExprRef {
    let bads: Vec<_> = sys
        .bad_states
        .iter()
        .map(|b| enc.get_at(ctx, *b, step))
        .collect();
    ctx.reduce_or(bads.into_iter())
}

fn state_equality(
    ctx: &mut Context,
    sys: &TransitionSystem,
    enc: &mut impl TransitionSystemEncoding,
    step0: u64,
    step1: u64,
) -> ExprRef {
    let mut out = ctx.get_true();
    for state in sys.states.iter() {
        let in_step0 = enc.get_at(ctx, state.symbol, step0);
        let in_step1 = enc.get_at(ctx, state.symbol, step1);
        let equals = ctx.equal(in_step0, in_step1);
        out = ctx.and(out, equals);
    }
    out
}

#[derive(Debug, Default)]
struct Pdr {
    frames: Vec<Frame>,
}

impl Pdr {
    fn push_frame(&mut self, ctx: &mut Context, smt: &mut impl SolverContext) -> Result<()> {
        let idx = self.frames.len() as u32;
        let label = ctx.bv_symbol(&format!("__frame_label_{idx}"), 1);
        smt.declare_const(ctx, label)?;
        self.frames.push(Frame {
            idx,
            label,
            formulas: vec![],
        });

        // TODO: add property constraint

        Ok(())
    }
}

#[derive(Debug)]
struct Frame {
    idx: u32,
    /// label |-> frame
    label: ExprRef,
    formulas: Vec<Formula>,
}

#[derive(Debug)]
struct Formula {
    expr: ExprRef,
    children: Vec<ExprRef>,
    kind: Kind,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Kind {
    Conjunction,
    Disjunction,
}
