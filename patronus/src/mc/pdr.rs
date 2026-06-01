// Copyright 2024-2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use std::cmp::{Ordering, Reverse};
use std::collections::BinaryHeap;
use std::sync::atomic::AtomicU64;
use crate::mc::bmc::TransitionSystemEncoding;
use crate::expr::*;
use crate::mc::{check_assuming, ModelCheckResult};
use crate::mc::bmc::start_bmc_or_pdr;
use crate::smt::*;
use crate::system::TransitionSystem;

type Result<T> = crate::smt::Result<T>;
type ClauseId = usize;

// Initial state constant
const INIT_STATE: u64 = 0;

// Current state constant
const CUR_STATE: u64 = 1;

// Next state constant
const NXT_STATE: u64 = 2;

// Maximum number of frames
const MAX_FRAMES: usize = 1000;

// Global activation literal counter
static ACT_COUNTER: AtomicU64 = AtomicU64::new(0);

// ------------------------------------------------------------------------------------------------
// Core PDR data structures
// ------------------------------------------------------------------------------------------------

trait Formula {
    /// Convert the formula into a conventional `ExprRef` SMT expression
    fn to_expr(&self, ctx: &mut Context) -> ExprRef;

    /// Negate the formula
    fn negate (&self, ctx: &mut Context) -> ExprRef;
}

/// `Cube` represents a conjunction of literals
#[derive(Debug, Default, Clone)]
struct Cube {
    literals: Vec<ExprRef>, // Set of literals
}

/// `Clause` represents a disjunction of literals
#[derive(Debug, Clone)]
struct Clause {
    act: ExprRef, // Activation literal
    literals: Vec<ExprRef>, // Set of literals
}

impl Formula for Cube {
    fn to_expr(&self, ctx: &mut Context) -> ExprRef {
        self.literals
            .iter()
            .cloned()
            .fold(ctx.get_true(), |acc, e| ctx.and(acc, e))
    }

    fn negate(&self, ctx: &mut Context) -> ExprRef {
        self.literals
            .iter()
            .cloned()
            .fold(
                ctx.get_false(),
                |acc, e| {
                    let neg_lit = ctx.not(e);
                    ctx.or(acc, neg_lit)
                }
            )
    }
}

impl Formula for Clause {
   fn to_expr(&self, ctx: &mut Context) -> ExprRef {
       self.literals
           .iter()
           .cloned()
           .fold(ctx.get_false(), |acc, e| ctx.or(acc, e))
   }
   fn negate(&self, ctx: &mut Context) -> ExprRef {
       self.literals
           .iter()
           .cloned()
           .fold(
               ctx.get_true(),
               |acc, e| {
                   let neg_lit = ctx.not(e);
                   ctx.and(acc, neg_lit)
                }
            )
   }
}

/// `ProofObj` is composed of a cube and a frame to block it at
struct ProofObj {
    cube: Cube,
    frame: usize,
}

// Custom comparators for `ProofObligation`
impl Eq for ProofObj {}
impl PartialEq for ProofObj {
    fn eq(&self, other: &Self) -> bool {
        self.frame.eq(&other.frame)
    }
}
impl PartialOrd for ProofObj {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for ProofObj {
    fn cmp(&self, other: &Self) -> Ordering {
        self.frame.cmp(&other.frame)
    }
}

// ------------------------------------------------------------------------------------------------
// Main PDR state and subroutines
// ------------------------------------------------------------------------------------------------

/// `PdrState` is the frames accumulated by PDR
///
/// **Representation Invariant**: `frames` must always have length > 0,
/// where the first frame is the initial frame and the last frame is the
/// infinite frame
#[derive(Debug, Default, Clone)]
struct PdrState {
    clauses: Vec<Clause>, // Collection of clauses used by PDR
    frames: Vec<Vec<ClauseId>>, // Delta trace of clauses in each frame
}

impl PdrState {
    /// Asserts the representation invariant
    #[inline]
    fn rep_ok(&self) {
        debug_assert!(self.frames.len() > 0);
    }

    fn new() -> Self {
        todo!("Finish implementation")
    }

    /// Return all clauses activation literals associated with a frame
    fn frame_assumptions(&self, frame_idx: usize) -> Vec<ExprRef> {
        self.frames[frame_idx]
            .iter()
            .copied()
            // Get all activation literals associated with clauses in the frame
            .map(|id| self.clauses[id].act)
            .collect()
    }

    // Extract the final state after SMT query
    fn extract_witness(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
        enc: &impl TransitionSystemEncoding) -> Result<Cube> {
        // Get bad state
        let mut bad_cube = Vec::with_capacity(sys.states.len());

        // Construct witness
        for state in &sys.states {
            let sym = enc.get_at(ctx, state.symbol, NXT_STATE);
            let val = smt_ctx.get_value(ctx, sym)?;
            let lit = ctx.equal(sym, val);
            bad_cube.push(lit);
        }

        Ok(Cube { literals: bad_cube })
    }

    /// Find a bad cube based on assertion of frontier frame (i.e. the last frame before
    /// the infinite frame)
    fn get_bad_cube(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
        enc: &impl TransitionSystemEncoding) -> Result<Option<Cube>> {
        // Frontier frame is frame before infinite frame
        let front_idx = self.frames.len() - 1;

        // Bad states
        let bad_states : Vec<ExprRef> =
            sys.bad_states
                .iter()
                .map(|b| enc.get_at(ctx, *b, NXT_STATE))
                .collect();

        // Bad variables to assert
        let mut bad_vars = ctx.get_false();

        for &bad in &bad_states {
            bad_vars = ctx.or(bad_vars, bad);
        }

        // Get activation literals for frame
        let mut assumptions = self.frame_assumptions(front_idx);
        assumptions.push(bad_vars);

        // Run SMT query (SAT?[F_f /\ P]), where F_f is the frontier frame and
        // P is the safety property
        match check_assuming(ctx, smt_ctx, assumptions)? {
            CheckSatResponse::Sat => Ok(Some(self.extract_witness(ctx, smt_ctx, sys, enc)?)),
            CheckSatResponse::Unsat => Ok(None),
            CheckSatResponse::Unknown => Err(
                Error::UnexpectedResponse(
                    String::from("`get_bad_cube`"),
                    String::from("unknown"),
                )
            ),
        }
    }

    /// Check for relative inductiveness by running the SMT query `SAT?[F_k /\ c /\ T /\ \neg c']`,
    /// where `F_k` is the relative frame, `c` is a cube, `c'` is the next state cube, and
    /// `T` is the transition relation
    ///
    /// Returns a `CheckSatResponse` with the query result
    fn rel_ind_check(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        proof_obj: &ProofObj) -> Result<CheckSatResponse> {
        // Start with frame assumptions
        let mut assumptions = self.frame_assumptions(proof_obj.frame);

        // Add `c` and `\neg c'` (transition relation is already in solver)
        { assumptions.push(proof_obj.cube.to_expr(&mut *ctx)); }
        { assumptions.push(proof_obj.cube.negate(&mut *ctx)); }

        Ok(check_assuming(ctx, smt_ctx, assumptions)?)
    }

    /// Check for relative inductiveness, but also return witness in case check fails
    ///
    /// **Note**: returns `Err` for `Unknown` relative inductiveness checks
    fn solve_relative(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
        enc: &impl TransitionSystemEncoding,
        proof_obj: &ProofObj) -> Result<Option<Cube>> {
        // Perform relative inductiveness check
        match self.rel_ind_check(ctx, smt_ctx, proof_obj)? {
            CheckSatResponse::Sat => Ok(Some(self.extract_witness(ctx, smt_ctx, sys, enc)?)),
            CheckSatResponse::Unsat => Ok(None), // Cube blocked by frame: no witness
            CheckSatResponse::Unknown => Err(
                Error::UnexpectedResponse(
                    String::from("`rel_ind_witness`"),
                    String::from("unknown `rel_ind_check`"),
                )
            )
        }
    }

    /// Generalize blocked cube with literal dropping
    ///
    /// Returns generalized cube
    fn generalize(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        proof_obj: &ProofObj) -> Result<Cube> {
        // Final remaining literals
        let mut rem_literals = Vec::new();

        for idx in 0..proof_obj.cube.literals.len() {
            let mut literals = proof_obj.cube.literals.clone();

            // Drop literal
            literals.swap_remove(idx);

            // Check if literal-dropped cube is still blocked by frame
            match self.rel_ind_check(ctx, smt_ctx, proof_obj)? {
                CheckSatResponse::Sat | CheckSatResponse::Unknown => rem_literals.push(
                    proof_obj.cube.literals[idx]
                ), // Unable to drop literal
                CheckSatResponse::Unsat => (), // Able to drop literal
            }
        }

        // Create new cube with unsuccessfully dropped literals
        Ok(Cube { literals: rem_literals })
    }

    /// Add blocked clause to frames
    fn add_clause(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        clause: &Clause) -> Result<()> {
        todo!("Finish implementation")
    }

    /// Try to block bad cube
    ///
    /// Returns whether cube was blocked successfully
    fn block_cube(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
        enc: &impl TransitionSystemEncoding,
        cube: &Cube) -> Result<bool> {
        // Check representation invariant
        self.rep_ok();

        // Min-queue for proof obligations
        let mut worklist = BinaryHeap::new();

        // Add first proof obligation (try to block at frontier frame)
        worklist.push(
            Reverse(
                ProofObj {
                    cube: cube.clone(),
                    frame: self.frames.len() - 1,
                }
            )
        );

        // Iterate through proof obligations
        while let Some(Reverse(proof_obj)) = worklist.pop() {
            // Check intersection with initial states
            if proof_obj.frame == 0 {
                return Ok(false)
            }

            match self.solve_relative(&mut *ctx, &mut *smt_ctx, sys, enc, &proof_obj)? {
                Some(wit) => {
                    // Cube was unable to be blocked: create new proof obligation
                    worklist.push(Reverse(
                        ProofObj {
                            cube: wit,
                            frame: self.frames.len() - 1,
                        }
                    ));
                    worklist.push(Reverse(proof_obj));
                }
                None => {
                    // Cube was blocked by frame: generalize and add to frames
                    let gen_cube = { self.generalize(&mut *ctx, &mut *smt_ctx, &proof_obj)? };
                    let mut gen_obj = ProofObj {
                        cube : gen_cube,
                        frame: proof_obj.frame,
                    };

                    // Push generalized cube to farthest possible frame
                    while gen_obj.frame < self.frames.len() {
                        match self.rel_ind_check(&mut *ctx, &mut *smt_ctx, &proof_obj)? {
                            // Relative inductiveness check fails: cannot move forward
                            CheckSatResponse::Sat | CheckSatResponse::Unknown => break,
                            // Relative inductiveness check succeeds: try next frame
                            CheckSatResponse::Unsat => gen_obj.frame += 1,
                        }
                    }

                    // Add generalized cube to frames
                    todo!("Finish implementation");
                }
            }
        }

        Ok(true)
    }

    /// Try to propagate all frame clauses to the next frame
    ///
    /// Returns whether Fixpoint reached (therefore signaling the termination of the algorithm)
    fn propagate_clauses(
        &mut self, ctx:
        &mut Context,
        smt_ctx: &mut impl SolverContext) -> Result<bool> {
        // Iterate though each frame
        for (idx, frame) in self.frames.clone().into_iter().enumerate() {
            // Skip first frame (initial state)
            if idx > 0 {
                let mut num_move = 0usize; // Number of clauses moved to the next frame

                // Iterate through each clause in the frame
                for &id in &frame {
                    // Get frame assumptions and add negated clause
                    let mut assumptions = self.frame_assumptions(idx);
                    assumptions.push(ctx.not(self.clauses[id].act));

                    // Run SMT query
                    match check_assuming(ctx, smt_ctx, assumptions)? {
                        CheckSatResponse::Sat | CheckSatResponse::Unknown => (), // Cannot move clause forward
                        CheckSatResponse::Unsat => {
                            // Move clause to the next frame
                            self.frames[idx + 1].push(id);
                            num_move += 1;
                        }
                    }

                    if num_move == frame.len() {
                        // Reached Fixpoint, return success
                        return Ok(true);
                    }
                }
            }
        }

        Ok(false)
    }
}

/// Public entrypoint for running PDR at most `MAX_FRAMES` frames
pub fn pdr(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
) -> Result<ModelCheckResult> {
    let mut enc = match start_bmc_or_pdr(ctx, smt_ctx, sys)? {
        (r, None) => return Ok(r),
        (_, Some(enc)) => enc,
    };

    // Check that system has states
    assert!(!sys.states.is_empty());

    // For now, only work with bitvectors
    smt_ctx.set_logic(Logic::QfBv)?;

    // Initialize system with reset state and starting inputs
    enc.init_at(ctx, smt_ctx, INIT_STATE)?;

    Ok(ModelCheckResult::Unknown)
}
