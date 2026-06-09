// Copyright 2024-2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use std::iter::once;
use baa::{BitVecOps, Value};
use rustc_hash::FxHashMap;
use crate::expr::*;
use crate::mc::{check_assuming, check_assuming_end, get_smt_value, ModelCheckResult, TransitionSystemEncoding};
use crate::mc::bmc::start_bmc_or_pdr;
use crate::smt::*;
use crate::smt::SmtCommand::SetOption;
use crate::system::TransitionSystem;

type Step = u64;
type CubeId = usize;

// Current step constant
const CUR_STEP: Step = 1;

// Next step constant
const NXT_STEP: Step = 2;

// Frame limit
const MAX_FRAMES: usize = 1000;

// -------------------------------------------------------------------------------------------------
// Core PDR data structures
// -------------------------------------------------------------------------------------------------

/// Methods on logic formulas
trait Formula {
    /// Convert this formula into an SMT expression
    fn to_expr(&self, ctx: &mut Context) -> ExprRef;

    /// Negate this formula into an SMT expression
    fn negate(&self, ctx: &mut Context) -> ExprRef;
}

/// A conjunction of literals
#[derive(Debug, Default, Clone)]
struct Cube {
    literals: Vec<ExprRef>, // Set of literals in conjunction
}

impl Formula for Cube {
    fn to_expr(&self, ctx: &mut Context) -> ExprRef {
        // Conjunct all literals
        self.literals
            .iter()
            .copied()
            .fold(ctx.get_true(), |acc, e| ctx.and(acc, e))
    }

    fn negate(&self, ctx: &mut Context) -> ExprRef {
        // Negate and then disjunct literals
        self.literals
            .iter()
            .copied()
            .fold(ctx.get_false(), |acc, e| {
                let neg_lit = ctx.not(e);
                ctx.or(acc, neg_lit)
            })
    }
}

/// Possible frame identifiers
#[derive(Debug, PartialOrd, PartialEq, Eq, Ord, Clone, Copy)]
enum FrameId {
    Step(usize), // Finite frame
    Infty, // Infinite frame
}

/// Cube and relevant frame identifier
#[derive(Debug, Clone)]
struct TimedCube {
    cube: Cube, // Cube
    frame: FrameId, // Frame identifier
}

// Custom comparators for `TimedCube` based on frame identifier
impl Eq for TimedCube {}
impl PartialEq for TimedCube {
    fn eq(&self, other: &Self) -> bool {
        self.frame.eq(&other.frame)
    }
}
impl Ord for TimedCube {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.frame.cmp(&other.frame)
    }
}
impl PartialOrd for TimedCube {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

// -------------------------------------------------------------------------------------------------
// PDR helper functions
// -------------------------------------------------------------------------------------------------

/// Get the stepped version of an SMT expresion
fn expr_at_step(
    ctx: &mut Context,
    enc: &impl TransitionSystemEncoding,
    expr: ExprRef,
    step: Step,
) -> ExprRef {
    simple_transform_expr(
        ctx,
        expr,
        |ctx, e, _ | {
            if ctx[e].is_symbol() {
                Some(enc.get_at(ctx, e, step))
            } else {
                None
            }
        }
    )
}

/// Extract states values from solver at a certain time step
///
/// **Requires**: previous SAT query
fn extract_state_values(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
    enc: &impl TransitionSystemEncoding,
    step: Step
) -> Result<Vec<Value>> {
    let mut state_vals = Vec::with_capacity(sys.states.len());

    // Extract exact SMT value for each system state
    for state in &sys.states {
        let sym = enc.get_at(ctx, state.symbol, step);
        state_vals.push(get_smt_value(ctx, smt_ctx, sym)?);
    }

    Ok(state_vals)
}

/// Extract input values from solver at a certain time step
///
/// **Requires**: previous SAT query
fn extract_input_values(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
    enc: &impl TransitionSystemEncoding,
    step: Step
) -> Result<Vec<Value>> {
    let mut input_vals = Vec::with_capacity(sys.states.len());

    // Get SMT value for each input
    for &input in &sys.inputs {
        let sym = enc.get_at(ctx, input, step);
        input_vals.push(get_smt_value(ctx, smt_ctx, sym)?);
    }

    Ok(input_vals)
}

/// Extract bitvector state assignment from solver as bit-level cubes
///
/// **Requires**: previous SAT query
fn get_bit_level_cube(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
    enc: &impl TransitionSystemEncoding,
    step: Step
) -> Result<Cube> {
    let mut literals = Vec::new();

    // Get state values
    let vals = extract_state_values(ctx, smt_ctx, sys, enc, step)?;

    assert_eq!(vals.len(), sys.states.len());

    // Iterate over all states and their corresponding values
    for (state, val) in sys.states.iter().zip(vals.iter()) {
        match val {
            Value::BitVec(bv) => {
                // Get bitvector width
                let width = bv.width();

                // Iterate through all bits of the bitvector
                // and assign bit-level equalities to concrete value
                for idx in 0..width {
                    let bit = ctx.slice(state.symbol, idx, idx);
                    let bit_val = if bv.is_bit_set(idx) {
                        ctx.get_true()
                    } else {
                        ctx.get_false()
                    };

                    let lit = ctx.equal(bit, bit_val);
                    literals.push(lit);
                }
            },
            Value::Array(_av) => todo!("Add array support"),
        }
    }

    Ok(Cube { literals })
}

/// Run `check-sat-assuming` query on solver and clean up afterwards
fn query(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    assumptions: impl IntoIterator<Item = ExprRef>
) -> Result<CheckSatResponse> {
    // Run SMT query and remove SMT frame
    let smt_res = check_assuming(ctx, smt_ctx, assumptions);
    check_assuming_end(smt_ctx)?;

    // Return result
    smt_res
}

// -------------------------------------------------------------------------------------------------
// Core PDR
// -------------------------------------------------------------------------------------------------

/// Functions maintained by all PDR implementations
trait Pdr {
    /// Returns frame identifier for frontier frame
    fn frontier(&self) -> FrameId;

    /// Try to extract safety property violation at frontier frame
    /// (i.e. `SAT?[R_N /\ \neg P]`)
    ///
    /// Returns `Some(cube)` with violation, else `None`
    ///
    /// **Note**: returns `Error::UnexpectedResponse` with `Unknown` query result
    fn get_bad_cube(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
        enc: &impl TransitionSystemEncoding
    ) -> Result<Option<Cube>>;

    /// Adds empty frame to frame trace
    fn add_frame(&mut self);

    /// Try to propagate blocked cubes in each frame to the next frame
    ///
    /// Returns whether fixpoint reached
    fn propagate_blocked_cubes(
        &mut self,
        smt_ctx: &mut impl SolverContext,
        enc: &impl TransitionSystemEncoding,
    ) -> Result<bool>;
}

/// Frame trace maintained by vanilla PDR
///
/// **Representation Invariant**: `frames.len() > 0`
struct BasePdr {
    cubes: FxHashMap<CubeId, Cube>, // Map between unique ID and blocked cubes
    frames: Vec<Vec<CubeId>>, // Frame trace containing frames with blocked cube identifiers
}

impl BasePdr {
    /// Initialize this PDR instance
    ///
    /// **Requires**: state variables to be stepped at two adjacent steps
    fn init(
        ctx: &mut Context,
        sys: &TransitionSystem,
        enc: &impl TransitionSystemEncoding
    ) -> Self {
        let mut init_cube = Cube::default();

        // Get all initial states from the system and create equalities between symbol
        // and initial values
        for state in &sys.states {
            if let Some(init) = state.init {
                let sym = enc.get_at(ctx, state.symbol, CUR_STEP);
                let lit = ctx.equal(sym, init);
                init_cube.literals.push(lit);
            }
        }

        Self {
            cubes: std::iter::once(init_cube).map(|e| (0, e)).collect(),
            frames: vec![vec![0usize]],
        }
    }

    /// Return list of clauses for non-init frames, or list of cubes for init frame
    ///
    /// **Note**: infinite frame unimplemented for `BasePdr`
    fn frame_assumptions(&self, ctx: &mut Context, frame: FrameId) -> ExprRef {
        assert_ne!(frame, FrameId::Infty);

        if let FrameId::Step(idx) = frame {
            assert!(idx < self.cubes.len());

            if idx == 0 {
                // Special case: init frame is just conjunction
                self.cubes[&0].to_expr(ctx)
            } else {
                // Else, just get conjunction of negated cubes (clauses)
                self.frames[idx]
                    .iter()
                    .fold(ctx.get_true(), |acc, id| {
                        let clause = self.cubes[id].negate(ctx);
                        ctx.and(acc, clause)
                    })
            }
        } else {
            // Should be unreachable
            panic!("No infinite frame in `BasePdr`")
        }
    }
}

impl Pdr for BasePdr {
    fn frontier(&self) -> FrameId {
        FrameId::Step(self.frames.len() - 1)
    }

    fn get_bad_cube(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
        enc: &impl TransitionSystemEncoding
    ) -> Result<Option<Cube>> {
        // Get frontier frame identifier
        let front = self.frontier();

        // Get next-state bad state literals
        let bad_lits: Vec<ExprRef> = sys.bad_states
            .iter()
            .map(|&b| expr_at_step(ctx, enc, b, NXT_STEP))
            .collect();

        // Disjunct all bad state literals
        let bad_expr = bad_lits
            .iter()
            .fold(ctx.get_false(), |acc, &b| ctx.or(acc, b));

        // Get frame assumptions for frontier frame
        let front_assumption = self.frame_assumptions(ctx, front);

        // Run query SAT?[R_N /\ \neg P]
        match query(ctx, smt_ctx, vec![front_assumption, bad_expr])? {
            CheckSatResponse::Sat => {
                // Safety property violation found: return witness cube
                let bad_cube = get_bit_level_cube(ctx, smt_ctx, sys, enc, NXT_STEP)?;
                Ok(Some(bad_cube))
            },
            CheckSatResponse::Unsat => Ok(None), // No safety property violation found
            CheckSatResponse::Unknown => Err( // Unknown query result: return error for soundness
                Error::UnexpectedResponse(
                    String::from("`get_bad_cube` in `BasePdr`"),
                    String::from("unknown query"),
                )
            )
        }
    }

    fn add_frame(&mut self) {
        self.frames.push(Vec::new());
    }

    fn propagate_blocked_cubes(
        &mut self,
        smt_ctx: &mut impl SolverContext,
        enc: &impl TransitionSystemEncoding
    ) -> Result<bool> {
        todo!()
    }
}

/// Runs PDR
pub fn pdr(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
) -> Result<ModelCheckResult> {
    let _enc = match start_bmc_or_pdr(ctx, smt_ctx, sys)? {
        (r, None) => return Ok(r),
        (_, Some(enc)) => enc,
    };

    Ok(ModelCheckResult::Unknown)
}
