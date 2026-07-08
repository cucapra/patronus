// Copyright 2025-2026 Cornell University
// released under BSD 3-Clause License
// author: Michael Zhang <mxz6@cornell.edu>, Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::*;
use crate::mc::bmc::start_bmc_or_pdr;
use crate::mc::encoding::TransitionSystemEncoding;
use crate::mc::{
    ModelCheckResult, UnrollSmtEncoding, bmc, check_assuming, check_assuming_end, get_smt_value,
};
use crate::smt::*;
use crate::system::TransitionSystem;
use baa::{BitVecOps, Value};
use rustc_hash::FxHashMap;
use::std::cell::RefCell;
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
// Public PDR interface structures
// -------------------------------------------------------------------------------------------------

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum PdrOption {
    /// Disable UNSAT core generalization
    DisableUnsatCores,
}

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
    enc: &mut PdrEncodingWrapper<impl TransitionSystemEncoding>,
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

/// Run `check-sat-assuming` query on solver, possibly extracting a model on `SAT` queries, or a
/// cube containing a subset of `assumptions` if `get_unsat_core` is true (yielded through `UNSAT`
/// core generalization)
///
/// # Returns
/// A pair containing the query result, and a solver model for `SAT` queries, or an `UNSAT` core
/// generalized cube if `get_unsat_core` is true
fn query(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
    enc: &mut PdrEncodingWrapper<impl TransitionSystemEncoding>,
    assumptions: impl IntoIterator<Item = ExprRef>,
    get_unsat_core: bool,
) -> Result<(CheckSatResponse, Option<Cube>)> {
    // Run SMT query and remove SMT frame
    let smt_res = check_assuming(ctx, smt_ctx, assumptions)?;

    // Extract appropriate model if `SAT`
    let out_cube = if smt_res == CheckSatResponse::Sat {
        let cex = get_bit_level_cube(ctx, smt_ctx, sys, enc, FROM_STEP)?;
        Some(cex)
    } else if smt_res == CheckSatResponse::Unsat && get_unsat_core {
        let unsat_assumps = smt_ctx.get_unsat_assumptions(ctx)?;
        Some(Cube {
            literals: unsat_assumps,
        })
    } else {
        None
    };

    check_assuming_end(smt_ctx)?;

    // Return result
    Ok((smt_res, out_cube))
}

// -------------------------------------------------------------------------------------------------
// PDR Transition System Encoding Wrapper
// -------------------------------------------------------------------------------------------------

/// Thin wrapper for [`TransitionSystemEncoding`] with stepped expression cache
struct PdrEncodingWrapper<E: TransitionSystemEncoding> {
    /// Stepped expression cache
    /// `(unstepped_expr, step) |-> stepped_expr @ step`
    expr_cache: FxHashMap<(ExprRef, Step), ExprRef>,

    /// Contained transition system encoding
    enc: E,
}

impl<E: TransitionSystemEncoding> PdrEncodingWrapper<E> {
    /// Create new [`TransitionSystemEncoding`] wrapper
    fn new(ctx: &mut Context, smt_ctx: &mut impl SolverContext, mut enc: E) -> Result<Self> {
        // Initialize encoding
        enc.init_at(ctx, smt_ctx, FROM_STEP)?;
        enc.unroll(ctx, smt_ctx)?;

        Ok(Self {
            expr_cache: FxHashMap::default(),
            enc,
        })
    }

    /// Step all symbol leaves in SMT expressions
    ///
    /// # Precondition
    /// All symbols in [expr] must be unstepped, and there must exist a stepped version of each
    /// symbol at [step] (unrolled in the original [`TransitionSystemEncoding`])
    fn expr_at_step(&mut self, ctx: &mut Context, expr: ExprRef, step: Step) -> ExprRef {
        if let Some(&sym) = self.expr_cache.get(&(expr, step)) {
            // If stepped expression already exists in cache, return cached version
            return sym;
        }

        // Yield final stepped expression
        let stepped = simple_transform_expr(ctx, expr, |ctx, e, _| {
            if ctx[e].is_symbol() {
                // Step expression
                let stepped = self.enc.get_signal_at(ctx, e, step);
                Some(stepped)
            } else {
                None
            }
        });

        // Add final stepped expression to cache
        self.expr_cache.insert((expr, step), stepped);
        stepped
    }
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

/// Frame trace maintained by vanilla PDR
struct BasePdr {
    /// Transition system encoding
    enc: PdrEncodingWrapper<UnrollSmtEncoding>,

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

    /// Whether to enable UNSAT core generalization
    unsat_cores_enabled: bool,
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
        enc: UnrollSmtEncoding,
        sys: &TransitionSystem,
        use_unsat_cores: bool,
    ) -> Result<Self> {
        // Wrap transition system encoding
        let mut enc = PdrEncodingWrapper::new(ctx, smt_ctx, enc)?;

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
            let cons_from = enc.expr_at_step(ctx, cons, FROM_STEP);
            smt_ctx.assert(ctx, cons_from)?;
        }

        // Next step constraint activation literal
        let cons_act = ctx.bv_symbol(format!("{ACT_LIT_PREFIX}to_cons").as_str(), 1);

        let cons_to_expr = sys
            .constraints
            .iter()
            .map(|&c| enc.expr_at_step(ctx, c, TO_STEP))
            .collect::<Vec<_>>()
            .into_iter()
            .fold(ctx.get_true(), |acc, c| ctx.and(acc, c));
        let cons_imp = ctx.implies(cons_act, cons_to_expr);

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
            enc,
            to_step_constraints_active: cons_act,
            init_frame: init_act,
            inf_frame,
            frames: vec![], // Index consistency taken care by indexing function
            next_act_id: 0,
            unsat_cores_enabled: use_unsat_cores,
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

    /// Check if assumptions intersect with the initial states
    ///
    /// # Returns
    /// Whether assumptions intersects with initial states and an optional `UNSAT` core cube
    /// on non-intersection if `get_unsat_core` is true
    ///
    /// # Errors
    /// Returns [`UnexpectedResponse`] if any SMT query returns `UNKNOWN`
    fn intersects_init(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
        enc: &impl TransitionSystemEncoding,
        assumptions: impl IntoIterator<Item = ExprRef>,
        get_unsat_core: bool,
    ) -> Result<(bool, Option<Cube>)> {
        // Initial frame
        let init = self.frame_assumptions(ctx, FrameId::Init);

        // Disable constraints for `TO_STEP`
        let neg_cons = ctx.not(self.to_step_constraints_active);

        // Complete assumptions
        let mut fin_assumps = vec![init, neg_cons];
        fin_assumps.extend(assumptions);

        // Run query `SAT?[R_0 /\ c]`
        let smt_res = query(ctx, smt_ctx, sys, enc, fin_assumps, get_unsat_core)?;

        if smt_res.0 == CheckSatResponse::Unknown {
            // Unknown query result: return error
            Err(UnexpectedResponse(
                "`intersects_init` in `BasePdr`".into(),
                "unknown query".into(),
            ))
        } else {
            // Else, only assert non-intersection if query was UNSAT
            Ok((smt_res.0 == CheckSatResponse::Sat, smt_res.1))
        }
    }

    /// "Fix" generalized cube by restoring enough removed literals until non-intersection
    /// with initial states
    ///
    /// # Errors
    /// Returns [`Error::UnexpectedResponse`] if any SMT query returns `UNKNOWN` or original cube
    /// truly intersects the initial states
    fn fix_gen_cube(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
        gen_cube: &Cube,
        rm_lits: impl IntoIterator<Item = ExprRef>,
    ) -> Result<Cube> {
        // If generalized cube already doesn't intersect with initial states, just return
        let cube_expr = gen_cube.to_expr(ctx);
        let cube_from = self.enc.expr_at_step(ctx, cube_expr, FROM_STEP);
        if self
            .intersects_init(ctx, smt_ctx, sys, [cube_from], false)?
            .0
        {
            return Ok(gen_cube);
        }

        // Map between activation literal and original unstepped literal
        let mut lit_map = FxHashMap::default();
        for lit in rm_lits {
            // Create activation literal implication
            let act = self.create_act_lit(ctx, smt_ctx)?;
            let expr_from = expr_at_step(ctx, enc, lit, FROM_STEP);
            let imp = ctx.implies(act, expr_from);

            // Assert in solver
            smt_ctx.assert(ctx, imp)?;

            // Add mapping
            lit_map.insert(act, lit);
        }

        // Flag for first iteration
        let mut first_iter = true;

        // Original generalized cube at `FROM_STEP`
        let cube_expr = gen_cube.to_expr(ctx);
        let cube_from = expr_at_step(ctx, enc, cube_expr, FROM_STEP);

        loop {
            // Initial intersection assumptions
            let mut fin_assumps = lit_map.keys().copied().collect::<Vec<_>>();

            // Add original generalized cube to assumption
            fin_assumps.push(cube_from);

            let check_res = self.intersects_init(ctx, smt_ctx, sys, fin_assumps, true)?;

            if check_res.0 && first_iter {
                // If first iteration, original cube must truly intersect with init frame
                return Err(UnexpectedResponse(
                    "`fix_gen_cube` in `BasePdr`".into(),
                    "original cube intersects with init".into(),
                ));
            }

            // All removed literals should not be in UNSAT core
            assert!(!check_res.0);

            // Store previous number of literals
            let prev_acts = lit_map.keys().copied().collect::<Vec<_>>();

            // Collect all literals in the UNSAT core
            let ex_cube = check_res.1.unwrap();
            let gen_lits = ex_cube.literals.iter().collect::<FxHashSet<_>>();

            // Remove all candidate literals not in UNSAT core
            lit_map.retain(|e, _| gen_lits.contains(e));

            // Permanently disable literals that were removed
            for &act in &prev_acts {
                if !lit_map.contains_key(&act) {
                    let neg_act = ctx.not(act);
                    smt_ctx.assert(ctx, neg_act)?;
                }
            }

            if lit_map.len() == prev_acts.len() {
                // If no literals are removed, then fixpoint reached
                let mut fin_lits = gen_cube.literals;
                fin_lits.extend(lit_map.values().copied());

                return Ok(Cube { literals: fin_lits });
            }

            first_iter = false;
        }
    }

    /// Run relative inductiveness query
    /// (i.e. `SAT?[R_{i - 1} /\ \neg c /\ T c']`)
    ///
    /// # Returns
    /// Query result and possibly a model for `SAT` cases, or a generalized cube if
    /// `unsat_core_enabled` is set in [`GLOB_PDR_OPTS`]
    fn rel_ind(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
        cube: &TimedCube,
        query_type: RelIndType,
    ) -> Result<(CheckSatResponse, Option<Cube>)> {
        // Query assumptions
        let mut assumptions = Vec::new();

        // Get frame assumption
        let frame_assumption = self.frame_assumptions(ctx, cube.frame.decrement());
        assumptions.push(frame_assumption);

        // Map between activation literal and original unstepped literal
        let mut lit_map = FxHashMap::default();
        for &lit in &cube.cube.literals {
            // Activate `TO_STEP` literal
            let act = self.create_act_lit(ctx, smt_ctx)?;
            let expr_to = enc.expr_at_step(ctx, lit, TO_STEP);
            let imp = ctx.implies(act, expr_to);

            // Permanently assert in solver
            smt_ctx.assert(ctx, imp)?;

            // Add mapping
            lit_map.insert(act, lit);
        }

        // Next step cube (expressed as `TO_STEP` literals)
        assumptions.extend(lit_map.keys());

        // Current step negation cube
        if query_type == RelIndType::Extended {
            let neg_cube_expr = cube.cube.negate(ctx);
            let neg_cube_from = self.enc.expr_at_step(ctx, neg_cube_expr, FROM_STEP);
            assumptions.push(neg_cube_from);
        }

        // Assert constraints hold after transition
        assumptions.push(self.to_step_constraints_active);

        // Run SMT query
        let smt_res = query(
            ctx,
            smt_ctx,
            sys,
            &mut self.enc,
            assumptions,
            self.unsat_cores_enabled,
        )?;

        // Extract candidate cube literals if generalized cube was created
        if smt_res.0 == CheckSatResponse::Unsat
            && let Some(genr) = smt_res.1
        {
            // Literals in UNSAT core
            let gen_lits = genr
                .literals
                .iter()
                .filter(|e| lit_map.contains_key(e))
                .map(|e| lit_map[e])
                .collect::<FxHashSet<_>>();

            // Literals not in UNSAT core
            let rm_lits = lit_map
                .values()
                .copied()
                .filter(|e| !gen_lits.contains(e))
                .collect::<Vec<_>>();

            // Make generalized cube not intersect initial states
            let gen_cube = Cube {
                literals: gen_lits.into_iter().collect(),
            };
            let fixed = self.fix_gen_cube(ctx, smt_ctx, sys, enc, gen_cube, rm_lits)?;

            // Disable all created activation literals
            for &act in lit_map.keys() {
                let neg_act = ctx.not(act);
                smt_ctx.assert(ctx, neg_act)?;
            }

            Ok((CheckSatResponse::Unsat, Some(fixed)))
        } else {
            Ok(smt_res)
        }
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
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
    ) -> Result<Option<Cube>> {
        // Get frontier frame identifier
        let front = self.frontier();

        // Get from-state bad state literals
        let bad_lits: Vec<ExprRef> = sys
            .bad_states
            .iter()
            .map(|&b| self.enc.expr_at_step(ctx, b, FROM_STEP))
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
            &mut self.enc,
            vec![front_assumption, bad_expr, neg_cons],
            false,
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

    fn add_blocked_cube(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        cube: TimedCube,
    ) -> Result<()> {
        // Create implication act_i => \neg c, where c is the blocked cube stepped at current step
        let clause = cube.cube.negate(ctx);
        let clause_expr = self.enc.expr_at_step(ctx, clause, FROM_STEP);
        let imp = ctx.implies(self[cube.frame].act, clause_expr);

        // Permanently assert implication in solver
        smt_ctx.assert(ctx, imp)?;

        // Add blocked cube to frame
        self[cube.frame].cubes.push(cube.cube);

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
        cube: TimedCube,
    ) -> Result<bool> {
        // Min-queue of proof obligations: start with initial proof obligation
        let mut worklist = BinaryHeap::from([cube]);

        // Try to solve all proof obligations
        while let Some(obj) = worklist.pop() {
            // If proof obligation intersects with initial states, blocking fails
            let obj_expr = obj.cube.to_expr(ctx);
            let obj_from = self.enc.expr_at_step(ctx, obj_expr, FROM_STEP);
            if self
                .intersects_init(ctx, smt_ctx, sys, enc, [obj_from], false)?
                .0
            {
                return Ok(false);
            }

            // Try to get counterexample relative to last frame
            let smt_res = self.rel_ind(ctx, smt_ctx, sys, &obj, RelIndType::Extended)?;
            let ex_cube = match smt_res {
                (CheckSatResponse::Sat, Some(cube)) => Some(cube), // Extract counterexample-to-induction
                (CheckSatResponse::Unsat, Some(gen_cube)) => Some(gen_cube), // Extract UNSAT core generalized cube
                (CheckSatResponse::Unsat, None) => None,                     // No generalized cube
                (CheckSatResponse::Unknown, _) => {
                    return Err(Error::UnexpectedResponse(
                        "`block_cube` in `BasePdr`".into(),
                        "unknown query".into(),
                    ));
                }
                _ => unreachable!(),
            };

            if smt_res.0 == CheckSatResponse::Sat
                && let Some(wit) = ex_cube
            {
                // Counterexample found: try to block predecessor and current obligation
                worklist.push(TimedCube {
                    cube: wit,
                    frame: obj.frame.decrement(),
                });
                worklist.push(obj);
            } else {
                // Extract generalized cube if there is one
                let cand_cube = if let Some(gen_cube) = ex_cube {
                    gen_cube
                } else {
                    obj.cube
                };

                let mut test_cube = TimedCube {
                    cube: cand_cube,
                    frame: obj.frame.increment(),
                };

                // Push cube as far as possible in the frame trace
                while test_cube.frame <= self.frontier()
                    && self
                        .rel_ind(ctx, smt_ctx, sys, &test_cube, RelIndType::Extended)?
                        .0
                        == CheckSatResponse::Unsat
                {
                    test_cube.frame = test_cube.frame.increment();
                }

                // Restore "working" frame
                test_cube.frame = test_cube.frame.decrement();

                // Refine frame trace with cube
                self.add_blocked_cube(ctx, smt_ctx, test_cube)?;
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
                    .rel_ind(ctx, smt_ctx, sys, &query_cube, RelIndType::Standard)?
                    .0;

                // Check that cube is still blocked in next frame
                if smt_res == CheckSatResponse::Unsat {
                    // Add blocked cube to next frame
                    self.add_blocked_cube(ctx, smt_ctx, query_cube)?;
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
                        self.add_blocked_cube(
                            ctx,
                            smt_ctx,
                            TimedCube {
                                cube,
                                frame: FrameId::Infinite,
                            },
                        )?;
                    }
                }

                return Ok(true);
            }
        }

        // Try to propagate all blocked cubes in the last finite frame into the infinite frame
        for cube in std::mem::take(&mut self[front].cubes) {
            let inf_assumption = self.frame_assumptions(ctx, FrameId::Infinite);

            let clause_expr = cube.negate(ctx);
            let clause_from = self.enc.expr_at_step(ctx, clause_expr, FROM_STEP);

            let cube_expr = cube.to_expr(ctx);
            let cube_to = self.enc.expr_at_step(ctx, cube_expr, TO_STEP);

            // Run the query `SAT?[R_\infty /\ \neg c /\ T /\ c']`, asserting that the
            // constraints hold at `TO_STEP`
            let smt_res = query(
                ctx,
                smt_ctx,
                sys,
                &mut self.enc,
                vec![
                    inf_assumption,
                    clause_from,
                    cube_to,
                    self.to_step_constraints_active,
                ],
                false,
            )?
            .0;

            if smt_res == CheckSatResponse::Unsat {
                // If UNSAT, blocked cube can also be propagated to infinite frame
                self.add_blocked_cube(
                    ctx,
                    smt_ctx,
                    TimedCube {
                        cube,
                        frame: FrameId::Infinite,
                    },
                )?;
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
    opts: impl IntoIterator<Item = PdrOption>,
) -> Result<ModelCheckResult> {
    let mut enc = match start_bmc_or_pdr(ctx, smt_ctx, sys)? {
        (r, None) => return Ok(r),
        (_, Some(enc)) => enc,
    };

    // Collect all options
    let sel_opts = opts.into_iter().collect::<FxHashSet<_>>();

    // Initialize two-step variables in solver
    enc.init_at(ctx, smt_ctx, FROM_STEP)?;
    enc.unroll(ctx, smt_ctx)?;

    // Initialize PDR
    let mut state = BasePdr::init(
        ctx,
        smt_ctx,
        enc,
        sys,
        !sel_opts.contains(&PdrOption::DisableUnsatCores),
    )?;

    let limit = FrameId::Finite(NonZeroUsize::new(MAX_FRAMES).unwrap());

    // PDR loop
    while state.frontier() <= limit {
        // Try to get bad cube
        let bad_cube = state.get_bad_cube(ctx, smt_ctx, sys)?;

        if let Some(bad) = bad_cube {
            // Try to block cube
            if !state.block_cube(
                ctx,
                smt_ctx,
                sys,
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
            if state.propagate_blocked_cubes(ctx, smt_ctx, sys)? {
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
