// Copyright 2024-2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::*;
use crate::mc::bmc::start_bmc_or_pdr;
use crate::mc::{
    ModelCheckResult, TransitionSystemEncoding, bmc, check_assuming, check_assuming_end,
    get_smt_value,
};
use crate::smt::*;
use crate::system::TransitionSystem;
use baa::{BitVecOps, Value};
use std::collections::BinaryHeap;

type Step = u64;

const FROM_STEP: Step = 1;

const TO_STEP: Step = 2;

const MAX_FRAMES: usize = 1000;

// -------------------------------------------------------------------------------------------------
// Core PDR data structures
// -------------------------------------------------------------------------------------------------

/// A conjunction of literals
#[derive(Debug, Clone)]
struct Cube {
    literals: Vec<ExprRef>,
}

impl Cube {
    /// Create an empty cube (i.e. `true`)
    const fn tru() -> Self {
        Self { literals: vec![] }
    }

    /// Convert this cube into an SMT expression
    fn to_expr(&self, ctx: &mut Context) -> ExprRef {
        // Conjunct all literals
        self.literals
            .iter()
            .copied()
            .fold(ctx.get_true(), |acc, e| ctx.and(acc, e))
    }

    /// Negate this cube into an SMT expression
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

type FrameId = usize;

/// Cube and relevant frame identifier
#[derive(Debug, Clone)]
struct TimedCube {
    cube: Cube,
    frame: usize,
}

// Equality comparators for `TimedCube`
// **NOTE**: comparators compare against the frame identifier, **NOT** the cube
//
// Therefore, a `TimedCube` is equal to another `TimedCube` iff the frame identifiers are the same.
//
// This simplifies the proof obligation queue ordering by avoiding a non-functional syntactic check
// on the cubes.
impl Eq for TimedCube {}
impl PartialEq for TimedCube {
    fn eq(&self, other: &Self) -> bool {
        self.frame.eq(&other.frame)
    }
}

// Ordering comparators for `TimedCube`
// **NOTE**: comparators compare against the frame identifier, **NOT** the cube
//
// A `TimedCube` with a _lower_ frame identifier is "greater" than another `TimedCube` with a
// _higher_ frame identifier.
//
// This simplifies the proof obligation queue ordering by avoiding the use of `Reverse` to enforce
// the min-queue ordering by frame identifiers for proof obligations.
impl Ord for TimedCube {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.frame.cmp(&self.frame)
    }
}
impl PartialOrd for TimedCube {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Relative Inductiveness Query types
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum RelIndType {
    /// Standard query (`SAT?[R_{i - 1} /\ T /\ c' ]`
    Standard,

    /// Extended query (`SAT?[R_{i - 1} /\ \neg c /\ T /\ c']`)
    Extended,
}

// -------------------------------------------------------------------------------------------------
// PDR helper functions
// -------------------------------------------------------------------------------------------------

/// Get the stepped version of an SMT expression
///
/// # Preconditions
/// * `expr` must exist in `enc` at `step`
fn expr_at_step(
    ctx: &mut Context,
    enc: &impl TransitionSystemEncoding,
    expr: ExprRef,
    step: Step,
) -> ExprRef {
    simple_transform_expr(ctx, expr, |ctx, e, _| {
        if ctx[e].is_symbol() {
            Some(enc.get_at(ctx, e, step))
        } else {
            None
        }
    })
}

/// Extract states values from solver at a certain time step
///
/// # Preconditions
/// * Must have previous `SAT` query
/// * `expr` must exist in `enc` at `step`
///
/// # Returns
/// [`Vec`] of pairs between original state symbol and value
fn extract_state_values(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
    enc: &impl TransitionSystemEncoding,
    step: Step,
) -> Result<Vec<(ExprRef, Value)>> {
    let mut state_vals = Vec::with_capacity(sys.states.len());

    // Extract exact SMT value for each system state
    for state in &sys.states {
        let sym = enc.get_at(ctx, state.symbol, step);
        state_vals.push((state.symbol, get_smt_value(ctx, smt_ctx, sym)?));
    }

    Ok(state_vals)
}

/// Extract bitvector state assignment from solver as bit-level cubes
///
/// # Preconditions
/// * Must have previous `SAT` query
/// * `expr` must exist in `enc` at `step`
fn get_bit_level_cube(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
    enc: &impl TransitionSystemEncoding,
    step: Step,
) -> Result<Cube> {
    let mut literals = Vec::new();

    // Get state values
    let vals = extract_state_values(ctx, smt_ctx, sys, enc, step)?;

    assert_eq!(vals.len(), sys.states.len());

    // Iterate over all states and their corresponding values
    for (sym, val) in vals {
        match val {
            Value::BitVec(bv) => {
                // Get bitvector width
                let width = bv.width();

                // Iterate through all bits of the bitvector
                // and assign bit-level equalities to concrete value
                for idx in 0..width {
                    let bit = ctx.slice(sym, idx, idx);
                    let bit_val = if bv.is_bit_set(idx) {
                        ctx.get_true()
                    } else {
                        ctx.get_false()
                    };

                    let lit = ctx.equal(bit, bit_val);
                    literals.push(lit);
                }
            }
            Value::Array(_av) => todo!("Add array support"),
        }
    }

    Ok(Cube { literals })
}

/// Run `check-sat-assuming` query on solver, possibly extracting a model on `SAT` queries
///
/// # Returns
/// A pair containing the query result, and a solver model from `SAT` queries
fn query(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
    enc: &impl TransitionSystemEncoding,
    assumptions: impl IntoIterator<Item = ExprRef>,
) -> Result<(CheckSatResponse, Option<Cube>)> {
    // Run SMT query and remove SMT frame
    let smt_res = check_assuming(ctx, smt_ctx, assumptions)?;

    // Extract appropriate model if `SAT`
    let model = if smt_res == CheckSatResponse::Sat {
        let cex = get_bit_level_cube(ctx, smt_ctx, sys, enc, FROM_STEP)?;
        Some(cex)
    } else {
        None
    };

    check_assuming_end(smt_ctx)?;

    // Return result
    Ok((smt_res, model))
}

// -------------------------------------------------------------------------------------------------
// Core PDR
// -------------------------------------------------------------------------------------------------

/// Frame trace maintained by vanilla PDR
///
/// **Representation Invariant**: `frames.len() > 0`
struct BasePdr {
    /// Frame trace containing frames with blocked cubes
    frames: Vec<Vec<Cube>>,
}

impl BasePdr {
    /// Initialize a PDR instance
    ///
    /// # Precondition
    /// State variables in transition system need to be stepped
    /// at two adjacent steps
    fn init(ctx: &mut Context, sys: &TransitionSystem) -> Self {
        let mut init_cube = Cube::tru();

        // Get all initial states from the system and create equalities between symbol
        // and initial values
        for state in &sys.states {
            if let Some(init) = state.init {
                let lit = ctx.equal(state.symbol, init);
                init_cube.literals.push(lit);
            }
        }

        Self {
            frames: vec![vec![init_cube]],
        }
    }

    /// # Returns
    /// * Clause representing non-init frame
    /// * Cube representing init frame
    fn frame_assumptions(&self, ctx: &mut Context, frame: FrameId) -> ExprRef {
        assert!(frame < self.frames.len());

        if frame == 0 {
            // Special case: init frame is just conjunction
            self.frames[0][0].to_expr(ctx)
        } else {
            // Else, just get conjunction of negated cubes (clauses)
            self.frames[frame].iter().fold(ctx.get_true(), |acc, cube| {
                let clause = cube.negate(ctx);
                ctx.and(acc, clause)
            })
        }
    }

    /// Run relative inductiveness query
    /// (i.e. `SAT?[R_{i - 1} /\ \neg c /\ T c']`)
    fn rel_ind(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
        enc: &impl TransitionSystemEncoding,
        cube: &TimedCube,
        query_type: RelIndType,
    ) -> Result<(CheckSatResponse, Option<Cube>)> {
        // Query assumptions
        let mut assumptions = Vec::new();

        // Get frame assumption
        let frame_assumption = self.frame_assumptions(ctx, cube.frame - 1);
        assumptions.push(expr_at_step(ctx, enc, frame_assumption, FROM_STEP));

        // Next step cube
        let cube_expr = cube.cube.to_expr(ctx);
        let cube_nxt = expr_at_step(ctx, enc, cube_expr, TO_STEP);
        assumptions.push(cube_nxt);

        // Current step negation cube
        if query_type == RelIndType::Extended {
            let neg_cube_expr = cube.cube.negate(ctx);
            let neg_cube_cur = expr_at_step(ctx, enc, neg_cube_expr, FROM_STEP);
            assumptions.push(neg_cube_cur);
        }

        // Run SMT query
        query(ctx, smt_ctx, sys, enc, assumptions)
    }

    /// Add blocked cubes to preceding frames
    ///
    /// # Preconditions
    /// Input cube must be blocked at frame `cube.frame`
    fn add_blocked_cube(&mut self, cube: &TimedCube) {
        // Get frontier index
        let front = cube.frame;

        // Add new cube to all frames
        for idx in 1..=front {
            self.frames[idx].push(cube.cube.clone());
        }
    }

    /// Frame identifier for frontier frame
    const fn frontier(&self) -> FrameId {
        self.frames.len() - 1
    }

    /// Try to extract safety property violation at frontier frame
    /// (i.e. `SAT?[R_N /\ \neg P]`)
    ///
    /// # Returns
    /// [`Some(Cube)`] with violation, else [`None`]
    ///
    /// # Errors
    /// In cases of `Unknown` SMT queries, return [`Error::UnexpectedResponse`]
    fn get_bad_cube(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
        enc: &impl TransitionSystemEncoding,
    ) -> Result<Option<Cube>> {
        // Get frontier frame identifier
        let front = self.frontier();

        // Get next-state bad state literals
        let bad_lits: Vec<ExprRef> = sys
            .bad_states
            .iter()
            .map(|&b| expr_at_step(ctx, enc, b, FROM_STEP))
            .collect();

        // Disjunct all bad state literals
        let bad_expr = bad_lits
            .iter()
            .fold(ctx.get_false(), |acc, &b| ctx.or(acc, b));

        // Get frame assumptions for frontier frame
        let front_assumption = self.frame_assumptions(ctx, front);
        let front_cur = expr_at_step(ctx, enc, front_assumption, FROM_STEP);

        // Run query SAT?[R_N /\ \neg P]
        match query(ctx, smt_ctx, sys, enc, vec![front_cur, bad_expr])? {
            (CheckSatResponse::Sat, Some(cube)) => {
                // Safety property violation found: return witness cube
                Ok(Some(cube))
            }
            (CheckSatResponse::Unsat, _) => Ok(None), // No safety property violation found
            (CheckSatResponse::Unknown, _) => Err(
                // Unknown query result: return error for soundness
                Error::UnexpectedResponse(
                    "`get_bad_cube` in `BasePdr`".into(),
                    "unknown query".into(),
                ),
            ),
            _ => unreachable!(),
        }
    }

    /// Adds empty frame to frame trace
    fn add_frame(&mut self) {
        self.frames.push(Vec::new());
    }

    /// Block cube in frame trace at certain frame
    ///
    /// # Returns
    /// Whether cube was successfully blocked
    ///
    /// # Errors
    /// In cases of `Unknown` SMT queries, return [`Error::UnexpectedResponse`]
    fn block_cube(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
        enc: &impl TransitionSystemEncoding,
        cube: &TimedCube,
    ) -> Result<bool> {
        // Min-queue of proof obligations: start with initial proof obligation
        let mut worklist = BinaryHeap::from([cube.clone()]);

        // Try to solve all proof obligations
        while let Some(obj) = worklist.pop() {
            // If initial frame reached, concrete counterexample trace found: fail
            if obj.frame == 0 {
                return Ok(false);
            }

            // Try to get counterexample relative to last frame
            let res = match self.rel_ind(ctx, smt_ctx, sys, enc, cube, RelIndType::Extended)? {
                (CheckSatResponse::Sat, Some(cube)) => Some(cube), // Extract counterexample-to-induction
                (CheckSatResponse::Unsat, _) => None,
                (CheckSatResponse::Unknown, _) => {
                    return Err(Error::UnexpectedResponse(
                        "`block_cube` in `BasePdr`".into(),
                        "unknown query".into(),
                    ));
                }
                _ => unreachable!(),
            };

            if let Some(wit) = res {
                // Counterexample found: try to block predecessor and current obligation
                worklist.push(TimedCube {
                    cube: wit,
                    frame: obj.frame - 1,
                });
                worklist.push(obj);
            } else {
                // Refine frame trace with cube
                self.add_blocked_cube(&obj);
            }
        }

        // All proof obligations blocked: success
        Ok(true)
    }

    /// Try to propagate blocked cubes in each frame to the next frame
    ///
    /// # Returns
    /// Whether fixpoint reached
    fn propagate_blocked_cubes(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
        enc: &impl TransitionSystemEncoding,
    ) -> Result<bool> {
        // Get frame index
        let front = self.frontier();

        // Try to propagate blocked cubes in each frame forward
        for idx in 1..front {
            let mut num_left = self.frames[idx].len();

            for cube_idx in 0..self.frames[idx].len() {
                // Get cube
                let cube = self.frames[idx][cube_idx].clone();

                // Get timed cube for relative inductiveness query
                let query_cube = TimedCube {
                    cube: cube.clone(),
                    frame: idx + 1,
                };

                // Check that cube is still blocked in next frame
                if self
                    .rel_ind(ctx, smt_ctx, sys, enc, &query_cube, RelIndType::Standard)?
                    .0
                    == CheckSatResponse::Unsat
                {
                    // Add blocked cube to next frame
                    self.frames[idx + 1].push(cube.clone());
                    num_left -= 1;
                }
            }

            // Check for inductive invariant: all clauses propagated
            if num_left == 0 {
                return Ok(true);
            }
        }

        // Inductive invariant not found
        Ok(false)
    }
}

/// Runs PDR algorithm on a finite-state transition system with a safety property
pub fn pdr(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
) -> Result<ModelCheckResult> {
    let mut enc = match start_bmc_or_pdr(ctx, smt_ctx, sys)? {
        (r, None) => return Ok(r),
        (_, Some(enc)) => enc,
    };

    // TODO: take care of constraints later
    assert!(sys.constraints.is_empty());

    // Initialize two-step variables in solver
    enc.init_at(ctx, smt_ctx, FROM_STEP)?;
    enc.unroll(ctx, smt_ctx)?;

    // Initialize PDR
    let mut state = BasePdr::init(ctx, sys);

    // PDR loop
    while state.frontier() <= MAX_FRAMES {
        // Try to get bad cube
        let bad_cube = state.get_bad_cube(ctx, smt_ctx, sys, &enc)?;

        if let Some(bad) = bad_cube {
            // Try to block cube
            if !state.block_cube(
                ctx,
                smt_ctx,
                sys,
                &enc,
                &TimedCube {
                    cube: bad,
                    frame: state.frontier(),
                },
            )? {
                // Reset solver
                smt_ctx.restart()?;

                // Cube could not be blocked: construct witness from BMC instance and fail
                let ModelCheckResult::Fail(wit) =
                    bmc(ctx, smt_ctx, sys, false, false, MAX_FRAMES as u64)?
                else {
                    unreachable!()
                };

                return Ok(ModelCheckResult::Fail(wit));
            }
        } else {
            // Add new frame
            state.add_frame();

            // Check if inductive invariant found
            if state.propagate_blocked_cubes(ctx, smt_ctx, sys, &enc)? {
                return Ok(ModelCheckResult::Success);
            }
        }
    }

    Ok(ModelCheckResult::Unknown)
}
