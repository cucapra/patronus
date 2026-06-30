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
use std::num::NonZeroUsize;
use std::ops::{Index, IndexMut};

type Step = u64;

const FROM_STEP: Step = 1;

const TO_STEP: Step = 2;

const MAX_FRAMES: usize = 1000;

/// Activation literal prefix
const ACT_LIT_PREFIX: &str = "__pdr_act_";

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

/// Cube and relevant frame identifier
#[derive(Debug, Clone)]
struct TimedCube {
    cube: Cube,
    frame: FrameId,
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

/// Equality is defined by constructor and inner fields (i.e. `FrameId::Init == FrameId::Init`,
/// `FrameId::Finite(5) == FrameId::Finite(5)`)
///
/// Comparison is defined as a partial order where `FrameId::Init` <= `FrameId::Finite` and
/// `FrameId::Finite` is compared against inner field
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum FrameId {
    /// Initial frame
    Init,

    /// Finite, non-initial frame
    Finite(NonZeroUsize),
}

impl FrameId {
    const fn increment(self) -> Self {
        match self {
            Self::Init => Self::Finite(NonZeroUsize::new(1).unwrap()),
            Self::Finite(n) => Self::Finite(NonZeroUsize::new(n.get() + 1).unwrap()),
        }
    }

    /// # Panics
    /// If [`FrameId::Init`] is decremented
    fn decrement(self) -> Self {
        match self {
            Self::Init => panic!("Cannot decrement init"),
            Self::Finite(n) => {
                let fin = n.get() - 1;

                if fin == 0 {
                    // Decremented to init frame
                    Self::Init
                } else {
                    Self::Finite(NonZeroUsize::new(fin).unwrap())
                }
            }
        }
    }
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

struct Frame {
    /// Frame activation literal
    act: ExprRef,

    /// Blocked cubes in frame
    cubes: Vec<Cube>,
}

impl Frame {
    fn add_blocked_cube(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        enc: &impl TransitionSystemEncoding,
        cube: &Cube,
    ) -> Result<()> {
        // Create implication act_i => \neg c, where c is the blocked cube stepped at current step
        let clause = cube.negate(ctx);
        let clause_expr = expr_at_step(ctx, enc, clause, FROM_STEP);
        let imp = ctx.implies(self.act, clause_expr);

        // Permanently assert implication in solver
        smt_ctx.assert(ctx, imp)?;

        // Add blocked cube to frame
        self.cubes.push(cube.clone());

        Ok(())
    }
}

/// Frame trace maintained by vanilla PDR
///
/// **Representation Invariant**: `frames.len() > 0`
struct BasePdr {
    /// Initial frame
    init_frame: ExprRef,

    /// Frame trace containing frames with blocked cubes
    frames: Vec<Frame>,

    /// Incrementing counter for creating unique frame activation literal IDs
    next_act_id: u64,
}

impl Index<FrameId> for BasePdr {
    type Output = Frame;

    /// # Panics
    /// When indexing init frame
    fn index(&self, index: FrameId) -> &Self::Output {
        match index {
            FrameId::Init => panic!("Cannot index init frame"), // Init frame doesn't explicitly exist
            FrameId::Finite(n) => &self.frames[n.get() - 1],
        }
    }
}

impl IndexMut<FrameId> for BasePdr {
    fn index_mut(&mut self, index: FrameId) -> &mut Self::Output {
        match index {
            FrameId::Init => panic!("Cannot index init frame"), // Init frame doesn't explicitly exist
            FrameId::Finite(n) => &mut self.frames[n.get() - 1],
        }
    }
}

/// Iterator method for [`BasePdr`]
impl BasePdr {
    fn iter(&'_ self) -> impl Iterator<Item = FrameId> + '_ {
        (1..=self.frames.len()).map(|ii| FrameId::Finite(NonZeroUsize::new(ii).unwrap()))
    }
}

impl BasePdr {
    /// Initialize a PDR instance
    ///
    /// # Precondition
    /// State variables in transition system need to be stepped
    /// at two adjacent steps
    fn init(
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        enc: &impl TransitionSystemEncoding,
        sys: &TransitionSystem,
    ) -> Result<Self> {
        let mut init_cube = Cube::tru();

        // Get all initial states from the system and create equalities between symbol
        // and initial values
        for state in &sys.states {
            if let Some(init) = state.init {
                let lit = ctx.equal(state.symbol, init);
                init_cube.literals.push(lit);
            }
        }

        // Initial frame activation literal
        let init_act = ctx.bv_symbol(format!("{ACT_LIT_PREFIX}_init").as_str(), 1);

        // Create act_0 => init_cube, where init_cube is stepped to the before step
        let init_expr = init_cube.to_expr(ctx);
        let init_expr = expr_at_step(ctx, enc, init_expr, FROM_STEP);
        let imp = ctx.implies(init_act, init_expr);

        // Permanently assert implication in solver
        smt_ctx.declare_const(ctx, init_act)?;
        smt_ctx.assert(ctx, imp)?;

        Ok(Self {
            init_frame: init_act,
            frames: vec![], // Index consistency taken care by indexing function
            next_act_id: 0,
        })
    }

    /// # Returns
    /// New activation literal
    fn create_act_lit(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
    ) -> Result<ExprRef> {
        let act = ctx.bv_symbol(format!("__pdr_act_{}", self.next_act_id).as_str(), 1);
        self.next_act_id += 1;

        smt_ctx.declare_const(ctx, act)?;

        Ok(act)
    }

    /// # Returns
    /// SMT expression asserting over-approximation of states reachable in `frame` steps
    /// (i.e. state space of `frame`-th frame), stepped at pre-transition step
    fn frame_assumptions(&self, ctx: &mut Context, frame_id: FrameId) -> ExprRef {
        if frame_id == FrameId::Init {
            // Special case: init frame is just activation literal for initial states
            self.init_frame
        } else {
            // Get conjunction with all other frame activation literals negated
            self.iter().fold(ctx.get_true(), |acc, id| {
                if id == frame_id {
                    // Include activation literals of target frame
                    ctx.and(acc, self[id].act)
                } else {
                    // Avoid solver bloat/slowdown by "disabling" other activation literals
                    //
                    // Sound since the actual state space represented by the `frame_id`-th
                    // frame is directly "activated" by `self[frame_id].act`. Allowing the solver
                    // to explore activation for the other frames would be redundant (for the
                    // upper frames) or unsound (for the lower frames)
                    //
                    // Note: must only "disable" lower frames once delta frames are implemented
                    let neg_act = ctx.not(self[id].act);
                    ctx.and(acc, neg_act)
                }
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
        let frame_assumption = self.frame_assumptions(ctx, cube.frame.decrement());
        assumptions.push(frame_assumption);

        // Next step cube
        let cube_expr = cube.cube.to_expr(ctx);
        let cube_next = expr_at_step(ctx, enc, cube_expr, TO_STEP);
        assumptions.push(cube_next);

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
    fn add_blocked_cube(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        enc: &impl TransitionSystemEncoding,
        cube: &TimedCube,
    ) -> Result<()> {
        // Get frontier index
        let front = cube.frame;

        // Get frame identifiers up to and including front index
        let ids = self
            .iter()
            .take_while(|id| id <= &front)
            .collect::<Vec<_>>();

        // Add new cube to all frames
        for id in ids {
            self[id].add_blocked_cube(ctx, smt_ctx, enc, &cube.cube)?;
        }

        Ok(())
    }

    /// Frame identifier for frontier frame
    const fn frontier(&self) -> FrameId {
        if self.frames.is_empty() {
            FrameId::Init
        } else {
            FrameId::Finite(NonZeroUsize::new(self.frames.len()).unwrap())
        }
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

        // Run query SAT?[R_N /\ \neg P]
        match query(ctx, smt_ctx, sys, enc, vec![front_assumption, bad_expr])? {
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
    fn add_frame(&mut self, ctx: &mut Context, smt_ctx: &mut impl SolverContext) -> Result<()> {
        // Create new activation literal for frame
        let act = self.create_act_lit(ctx, smt_ctx)?;

        // Add new frame
        self.frames.push(Frame { act, cubes: vec![] });

        Ok(())
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
            if obj.frame == FrameId::Init {
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
                    frame: obj.frame.decrement(),
                });
                worklist.push(obj);
            } else {
                // Refine frame trace with cube
                self.add_blocked_cube(ctx, smt_ctx, enc, &obj)?;
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

        // Get ids until the front identifier
        let ids = self.iter().take_while(|id| id < &front).collect::<Vec<_>>();

        // Try to propagate blocked cubes in each frame forward
        for id in ids {
            let mut num_left = self[id].cubes.len();

            for cube_idx in 0..self[id].cubes.len() {
                // Get cube
                let cube = self[id].cubes[cube_idx].clone();

                // Get timed cube for relative inductiveness query
                let query_cube = TimedCube {
                    cube: cube.clone(),
                    frame: id.increment(),
                };

                // Check that cube is still blocked in next frame
                if self
                    .rel_ind(ctx, smt_ctx, sys, enc, &query_cube, RelIndType::Standard)?
                    .0
                    == CheckSatResponse::Unsat
                {
                    // Add blocked cube to next frame
                    self[id.increment()].add_blocked_cube(ctx, smt_ctx, enc, &cube)?;
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
    let mut state = BasePdr::init(ctx, smt_ctx, &enc, sys)?;

    // PDR loop
    while state.frontier() <= FrameId::Finite(NonZeroUsize::new(MAX_FRAMES).unwrap()) {
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
            state.add_frame(ctx, smt_ctx)?;

            // Check if inductive invariant found
            if state.propagate_blocked_cubes(ctx, smt_ctx, sys, &enc)? {
                return Ok(ModelCheckResult::Success);
            }
        }
    }

    Ok(ModelCheckResult::Unknown)
}

mod tests {
    use super::*;

    #[test]
    fn test_frame_id_cmp() {
        assert!(FrameId::Init < FrameId::Finite(NonZeroUsize::new(1).unwrap()));
        assert!(FrameId::Init < FrameId::Finite(NonZeroUsize::new(5).unwrap()));
        assert!(
            FrameId::Finite(NonZeroUsize::new(3).unwrap())
                < FrameId::Finite(NonZeroUsize::new(5).unwrap())
        );
        assert!(FrameId::Init >= FrameId::Init);
        assert!(
            FrameId::Finite(NonZeroUsize::new(5).unwrap())
                >= FrameId::Finite(NonZeroUsize::new(5).unwrap())
        );
    }

    #[test]
    fn test_frame_id_eq() {
        assert_ne!(
            FrameId::Init,
            FrameId::Finite(NonZeroUsize::new(1).unwrap())
        );
        assert_ne!(
            FrameId::Finite(NonZeroUsize::new(2).unwrap()),
            FrameId::Finite(NonZeroUsize::new(1).unwrap())
        );
        assert_eq!(FrameId::Init, FrameId::Init);
        assert_eq!(
            FrameId::Finite(NonZeroUsize::new(1).unwrap()),
            FrameId::Finite(NonZeroUsize::new(1).unwrap())
        );
    }
}
