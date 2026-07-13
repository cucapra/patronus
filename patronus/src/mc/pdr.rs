// Copyright 2025-2026 Cornell University
// released under BSD 3-Clause License
// author: Michael Zhang <mxz6@cornell.edu>, Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::*;
use crate::mc::bmc::start_bmc_or_pdr;
use crate::mc::encoding::TransitionSystemEncoding;
use crate::mc::utils::{check_assuming, check_assuming_end, get_smt_value};
use crate::mc::{ModelCheckResult, bmc};
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

    /// Infinite frame
    Infinite,
}

impl FrameId {
    const fn increment(self) -> Self {
        match self {
            Self::Init => Self::Finite(NonZeroUsize::new(1).unwrap()),
            Self::Finite(n) => Self::Finite(NonZeroUsize::new(n.get() + 1).unwrap()),
            Self::Infinite => panic!("cannot increment infinite frame"),
        }
    }

    /// # Panics
    /// If [`FrameId::Init`] is decremented
    fn decrement(self) -> Self {
        match self {
            Self::Init => panic!("cannot decrement init"),
            Self::Finite(n) => {
                let fin = n.get() - 1;

                if fin == 0 {
                    // Decremented to init frame
                    Self::Init
                } else {
                    Self::Finite(NonZeroUsize::new(fin).unwrap())
                }
            }
            Self::Infinite => panic!("cannot decrement infinite frame"),
        }
    }
}

// -------------------------------------------------------------------------------------------------
// PDR helper functions
// -------------------------------------------------------------------------------------------------

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
        let sym = enc.expr_at_step(ctx, state.symbol, step);
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
                    let lit = if bv.is_bit_set(idx) {
                        bit
                    } else {
                        ctx.not(bit)
                    };

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
        cube: Cube,
    ) -> Result<()> {
        // Create implication act_i => \neg c, where c is the blocked cube stepped at current step
        let clause = cube.negate(ctx);
        let clause_expr = enc.expr_at_step(ctx, clause, FROM_STEP);
        let imp = ctx.implies(self.act, clause_expr);

        // Permanently assert implication in solver
        smt_ctx.assert(ctx, imp)?;

        // Add blocked cube to frame
        self.cubes.push(cube);

        Ok(())
    }
}

/// Frame trace maintained by vanilla PDR
struct BasePdr {
    /// `TO_STEP` constraints
    to_step_constraints_active: ExprRef,

    /// Initial frame
    init_frame: ExprRef,

    /// Infinite frame
    inf_frame: Frame,

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
            FrameId::Infinite => &self.inf_frame,
        }
    }
}

impl IndexMut<FrameId> for BasePdr {
    fn index_mut(&mut self, index: FrameId) -> &mut Self::Output {
        match index {
            FrameId::Init => panic!("Cannot index init frame"), // Init frame doesn't explicitly exist
            FrameId::Finite(n) => &mut self.frames[n.get() - 1],
            FrameId::Infinite => &mut self.inf_frame,
        }
    }
}

/// Iterator method for [`BasePdr`]
impl BasePdr {
    fn iter(&'_ self) -> impl Iterator<Item = FrameId> + '_ {
        (1..=(self.frames.len() + 1)).map(|ii| {
            if ii <= self.frames.len() {
                FrameId::Finite(NonZeroUsize::new(ii).unwrap())
            } else {
                // Last frame is the infinite frame
                FrameId::Infinite
            }
        })
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

        // Always assert constraints at current step
        for &cons in &sys.constraints {
            let cons_cur = enc.expr_at_step(ctx, cons, FROM_STEP);
            smt_ctx.assert(ctx, cons_cur)?;
        }

        // Next step constraint activation literal
        let cons_act = ctx.bv_symbol(format!("{ACT_LIT_PREFIX}nxt_cons").as_str(), 1);

        let cons_next_expr = sys
            .constraints
            .iter()
            .map(|&c| enc.expr_at_step(ctx, c, TO_STEP))
            .collect::<Vec<_>>()
            .into_iter()
            .fold(ctx.get_true(), |acc, c| ctx.and(acc, c));
        let cons_imp = ctx.implies(cons_act, cons_next_expr);

        // Permanently assert in solver
        smt_ctx.declare_const(ctx, cons_act)?;
        smt_ctx.assert(ctx, cons_imp)?;

        // Initial frame activation literal
        let init_act = ctx.bv_symbol(format!("{ACT_LIT_PREFIX}init").as_str(), 1);

        // Create act_0 => init_cube, where init_cube is stepped to the before step
        let init_expr = init_cube.to_expr(ctx);
        let init_expr = enc.expr_at_step(ctx, init_expr, FROM_STEP);
        let init_imp = ctx.implies(init_act, init_expr);

        // Permanently assert implication in solver
        smt_ctx.declare_const(ctx, init_act)?;
        smt_ctx.assert(ctx, init_imp)?;

        // Create infinite frame
        let inf_act = ctx.bv_symbol(format!("{ACT_LIT_PREFIX}inf").as_str(), 1);
        smt_ctx.declare_const(ctx, inf_act)?;
        let inf_frame = Frame {
            act: inf_act,
            cubes: vec![],
        };

        Ok(Self {
            to_step_constraints_active: cons_act,
            init_frame: init_act,
            inf_frame,
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
        let act = ctx.bv_symbol(format!("{ACT_LIT_PREFIX}{}", self.next_act_id).as_str(), 1);
        self.next_act_id += 1;

        smt_ctx.declare_const(ctx, act)?;

        Ok(act)
    }

    /// # Returns
    /// SMT expression asserting over-approximation of states reachable in `frame` steps
    /// (i.e. state space of `frame`-th frame), stepped at pre-transition step
    fn frame_assumptions(&self, ctx: &mut Context, frame_id: FrameId) -> ExprRef {
        assert!(
            frame_id == FrameId::Init
                || frame_id <= self.frontier()
                || frame_id == FrameId::Infinite
        );

        // Special case: for init frame, just return initial activation literal
        if frame_id == FrameId::Init {
            return self.iter().fold(self.init_frame, |acc, id| {
                let neg_act = ctx.not(self[id].act);
                ctx.and(acc, neg_act)
            });
        }

        // Conjunct all blocked cubes in this frame and higher (since all blocked
        // cubes in higher delta frames are also blocked in this frame)
        self.iter().fold(ctx.not(self.init_frame), |acc, id| {
            if id >= frame_id {
                // Include activation literals of target frame and all higher frames,
                // which include cubes blocked in the `frame_id`-th frame
                ctx.and(acc, self[id].act)
            } else {
                // Deactivate lower frames to preserve soundness,
                // since they represent overapproximations of reachable state
                // that are stronger than that of the `frame_id`-th frame
                let neg_act = ctx.not(self[id].act);
                ctx.and(acc, neg_act)
            }
        })
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
        let cube_next = enc.expr_at_step(ctx, cube_expr, TO_STEP);
        assumptions.push(cube_next);

        // Current step negation cube
        if query_type == RelIndType::Extended {
            let neg_cube_expr = cube.cube.negate(ctx);
            let neg_cube_cur = enc.expr_at_step(ctx, neg_cube_expr, FROM_STEP);
            assumptions.push(neg_cube_cur);
        }

        // Assert constraints hold after transition
        assumptions.push(self.to_step_constraints_active);

        // Run SMT query
        query(ctx, smt_ctx, sys, enc, assumptions)
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
            .map(|&b| enc.expr_at_step(ctx, b, FROM_STEP))
            .collect();

        // Disjunct all bad state literals
        let bad_expr = bad_lits
            .iter()
            .fold(ctx.get_false(), |acc, &b| ctx.or(acc, b));

        // Get frame assumptions for frontier frame
        let front_assumption = self.frame_assumptions(ctx, front);

        // Turn off constraint requirements for `TO_STEP`
        let neg_cons = ctx.not(self.to_step_constraints_active);

        // Run query SAT?[R_N /\ \neg P]
        match query(
            ctx,
            smt_ctx,
            sys,
            enc,
            vec![front_assumption, bad_expr, neg_cons],
        )? {
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
        cube: TimedCube,
    ) -> Result<bool> {
        // Min-queue of proof obligations: start with initial proof obligation
        let mut worklist = BinaryHeap::from([cube]);

        // Try to solve all proof obligations
        while let Some(obj) = worklist.pop() {
            // If initial frame reached, concrete counterexample trace found: fail
            if obj.frame == FrameId::Init {
                return Ok(false);
            }

            // Try to get counterexample relative to last frame
            let res = match self.rel_ind(ctx, smt_ctx, sys, enc, &obj, RelIndType::Extended)? {
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
                let mut test_cube = TimedCube {
                    cube: obj.cube.clone(),
                    frame: obj.frame.increment(),
                };

                // Push cube as far as possible in the frame trace
                while test_cube.frame <= self.frontier()
                    && self
                        .rel_ind(ctx, smt_ctx, sys, enc, &test_cube, RelIndType::Extended)?
                        .0
                        == CheckSatResponse::Unsat
                {
                    test_cube.frame = test_cube.frame.increment();
                }

                // Restore "working" frame
                test_cube.frame = test_cube.frame.decrement();

                // Refine frame trace with cube
                self[test_cube.frame].add_blocked_cube(ctx, smt_ctx, enc, test_cube.cube)?;
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
        let front = self.frontier();

        // Get identifiers for all finite frames (except the last, where a blocked cube
        // cannot be propagated from a finite frame to an infinite frame)
        let ids = self.iter().take_while(|id| id < &front).collect::<Vec<_>>();

        // Try to propagate blocked cubes in each frame forward
        for id in ids {
            for cube in std::mem::take(&mut self[id].cubes) {
                // Get timed cube for relative inductiveness query
                let query_cube = TimedCube {
                    cube,
                    frame: id.increment(),
                };

                // Run query `SAT?[R_i /\ T /\ c]`, where `c` is the candidate cube
                // for propagation
                let smt_res = self
                    .rel_ind(ctx, smt_ctx, sys, enc, &query_cube, RelIndType::Standard)?
                    .0;

                // Check that cube is still blocked in next frame
                if smt_res == CheckSatResponse::Unsat {
                    // Add blocked cube to next frame
                    self[id.increment()].add_blocked_cube(ctx, smt_ctx, enc, query_cube.cube)?;
                } else {
                    // Query must have been SAT or UNKNOWN: do not propagate to ensure soundness
                    self[id].cubes.push(query_cube.cube);
                }
            }

            // Check for inductive invariant: all clauses propagated
            if self[id].cubes.is_empty() {
                // Collect all frame IDs from this frame to just before infinite frame
                let inv_ids = self
                    .iter()
                    .filter(|iid| iid > &id && iid < &FrameId::Infinite)
                    .collect::<Vec<_>>();

                // Add all learned invariants to infinite frame
                for iid in inv_ids {
                    for cube in std::mem::take(&mut self[iid].cubes) {
                        self[FrameId::Infinite].add_blocked_cube(ctx, smt_ctx, enc, cube)?;
                    }
                }

                return Ok(true);
            }
        }

        // Try to propagate all blocked cubes in the last finite frame into the infinite frame
        for cube in std::mem::take(&mut self[front].cubes) {
            let inf_assumption = self.frame_assumptions(ctx, FrameId::Infinite);

            let clause_expr = cube.negate(ctx);
            let clause_cur = enc.expr_at_step(ctx, clause_expr, FROM_STEP);

            let cube_expr = cube.to_expr(ctx);
            let cube_next = enc.expr_at_step(ctx, cube_expr, TO_STEP);

            // Run the query `SAT?[R_\infty /\ \neg c /\ T /\ c']`, asserting that the
            // constraints hold at `TO_STEP`
            let smt_res = query(
                ctx,
                smt_ctx,
                sys,
                enc,
                vec![
                    inf_assumption,
                    clause_cur,
                    cube_next,
                    self.to_step_constraints_active,
                ],
            )?
            .0;

            if smt_res == CheckSatResponse::Unsat {
                // If UNSAT, blocked cube can also be propagated to infinite frame
                self[FrameId::Infinite].add_blocked_cube(ctx, smt_ctx, enc, cube)?;
            } else {
                // Else, blocked cube can only stay in finite frame
                self[front].cubes.push(cube);
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

    // Initialize two-step variables in solver
    enc.init_at(ctx, smt_ctx, FROM_STEP)?;
    enc.unroll(ctx, smt_ctx)?;

    // Initialize PDR
    let mut state = BasePdr::init(ctx, smt_ctx, &enc, sys)?;

    let limit = FrameId::Finite(NonZeroUsize::new(MAX_FRAMES).unwrap());

    // PDR loop
    while state.frontier() <= limit {
        // Try to get bad cube
        let bad_cube = state.get_bad_cube(ctx, smt_ctx, sys, &enc)?;

        if let Some(bad) = bad_cube {
            // Try to block cube
            if !state.block_cube(
                ctx,
                smt_ctx,
                sys,
                &enc,
                TimedCube {
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

#[cfg(test)]
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

        assert!(FrameId::Init < FrameId::Infinite);
        assert!(FrameId::Infinite >= FrameId::Infinite);
        assert!(FrameId::Finite(NonZeroUsize::new(5).unwrap()) < FrameId::Infinite);
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
        assert_ne!(FrameId::Init, FrameId::Infinite);
        assert_ne!(
            FrameId::Infinite,
            FrameId::Finite(NonZeroUsize::new(5).unwrap())
        );
        assert_eq!(FrameId::Init, FrameId::Init);
        assert_eq!(
            FrameId::Finite(NonZeroUsize::new(1).unwrap()),
            FrameId::Finite(NonZeroUsize::new(1).unwrap())
        );
        assert_eq!(FrameId::Infinite, FrameId::Infinite);
    }
}
