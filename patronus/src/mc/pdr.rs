// Copyright 2024-2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::iter::once;
use std::rc::Rc;
use baa::{ArrayOps, BitVecOps, BitVecValue, Value};
use rustc_hash::FxHashMap;
use crate::expr::*;
use crate::mc::{check_assuming, check_assuming_end, get_smt_value, InitValue, ModelCheckResult, TransitionSystemEncoding, Witness};
use crate::mc::bmc::start_bmc_or_pdr;
use crate::smt::*;
use crate::system::TransitionSystem;

type Step = u64;
type CubeId = usize;

/// Current step constant
const CUR_STEP: Step = 1;

/// Next step constant
const NXT_STEP: Step = 2;

/// Frame limit
const MAX_FRAMES: usize = 1000;

// -------------------------------------------------------------------------------------------------
// Core PDR data structures
// -------------------------------------------------------------------------------------------------

/// Methods on logic formulas
trait Formula {
    /// Convert this formula into an SMT expression
    ///
    /// # Arguments
    /// * `ctx` - SMT expression context
    ///
    /// # Returns
    /// SMT expression representing this logic formula
    fn to_expr(&self, ctx: &mut Context) -> ExprRef;

    /// Negate this formula into an SMT expression
    ///
    /// # Arguments
    /// * `ctx` - SMT expression context
    ///
    /// # Returns
    /// SMT expression representing the negated logic formula
    fn negate(&self, ctx: &mut Context) -> ExprRef;
}

/// A conjunction of literals
#[derive(Debug, Default, Clone)]
struct Cube {
    /// Set of literals in cube
    literals: Vec<ExprRef>,
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
    /// Finite frame with associated index
    Step(usize),

    /// Infinite frame
    Infty,
}

impl FrameId {
    /// Decrement frame index for finite frame ID
    ///
    /// # Returns
    /// Decremented frame ID
    fn decrement(&self) -> Self {
        if let Self::Step(step) = self {
            Self::Step(step - 1)
        } else {
            Self::Infty
        }
    }

    /// Get some finite frame index
    ///
    /// # Returns
    /// [`Some(step)`] for finite identifiers, else [`None`] for infinite identifiers
    const fn get_step(&self) -> Option<usize> {
        if let Self::Step(step) = self {
            Some(*step)
        } else {
            None
        }
    }
}

/// Cube and relevant frame identifier
#[derive(Debug, Clone)]
struct TimedCube {
    /// Cube
    cube: Cube,

    /// Some frame associated with cube
    frame: FrameId,
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

/// Relative Inductiveness Query types
#[derive(Debug, Clone, PartialEq, Eq)]
enum RelIndType {
    /// Standard query (`SAT?[R_{i - 1} /\ T /\ c' ]`
    Standard,

    /// Extended query (`SAT?[R_{i - 1} /\ \neg c /\ T /\ c']`)
    Extended,
}

/// Node in counterexample trace
#[derive(Debug, Clone)]
struct CexEntry {
    /// Pairs of state symbols and values
    states: Vec<(ExprRef, Value)>,

    /// Pairs of input symbols and values
    inputs: Vec<(ExprRef, Value)>,

    /// Pointer to next state (successor) in counterexample trace
    next: Option<Rc<Self>>,
}

/// Proof obligation contains cube and counterexample trace start
struct ProofObj(TimedCube, Rc<CexEntry>);

/// Custom comparators
impl Eq for ProofObj {}
impl PartialEq for ProofObj {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}
impl Ord for ProofObj {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}
impl PartialOrd for ProofObj {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

// -------------------------------------------------------------------------------------------------
// PDR helper functions
// -------------------------------------------------------------------------------------------------

/// Get the stepped version of an SMT expression
///
/// # Arguments
/// * `ctx` - SMT expression context
/// * `enc` - Transition system encoding
/// * `expr` - SMT expression to step
/// * `step` - Step number (**Requires**: step to exist in solver)
///
/// # Returns
/// Stepped version of original SMT expression
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
/// # Preconditions
/// Must have previous SAT query
///
/// # Arguments
/// * `ctx` - SMT expression context
/// * `smt_ctx` - SMT solver
/// * `sys` - Transition system information
/// * `enc` - Transition system encoding
/// * `step` - Step to extract state values from (**Requires**: step to exist in solver)
///
/// # Returns s
/// [`Vec`] of pairs with original stateymbol and value
///
/// # Errors
/// SMT solver crashes (most likely due to precondition violations)
fn extract_state_values(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
    enc: &impl TransitionSystemEncoding,
    step: Step
) -> Result<Vec<(ExprRef, Value)>> {
    let mut state_vals = Vec::with_capacity(sys.states.len());

    // Extract exact SMT value for each system state
    for state in &sys.states {
        let sym = enc.get_at(ctx, state.symbol, step);
        state_vals.push((state.symbol, get_smt_value(ctx, smt_ctx, sym)?));
    }

    Ok(state_vals)
}

/// Extract input values from solver at a certain time step
///
/// # Preconditions
/// Must have previous SAT query
///
/// # Arguments
/// * `ctx` - SMT expression context
/// * `smt_ctx` - SMT solver
/// * `sys` - Transition system information
/// * `enc` - Transition system encoding
///
/// # Returns
/// [`Vec`] of pairs with original input symbol and value
///
/// # Errors
/// SMT solver crashes (most likely due to precondition violations)
fn extract_input_values(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
    enc: &impl TransitionSystemEncoding,
) -> Result<Vec<(ExprRef, Value)>> {
    let mut input_vals = Vec::with_capacity(sys.states.len());

    // Get SMT value for each input
    for &input in &sys.inputs {
        let sym = enc.get_at(ctx, input, CUR_STEP);
        input_vals.push((input, get_smt_value(ctx, smt_ctx, sym)?));
    }

    Ok(input_vals)
}

/// Extract bitvector state assignment from solver as bit-level cubes
///
/// # Preconditions
/// Must have previous SAT query
///
/// # Arguments
/// * `ctx` - SMT expression context
/// * `smt_ctx` - SMT solver
/// * `sys` - Transition system information
/// * `enc` - Transition system encoding
/// * `step` - Step to extract state values from (**Requires**: step to exist in solver)
///
/// # Returns
/// Cube of bitwise equalities representing state values
///
/// # Errors
/// SMT solver crashes (most likely due to precondition violations)
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
            },
            Value::Array(_av) => todo!("Add array support"),
        }
    }

    Ok(Cube { literals })
}

/// Run `check-sat-assuming` query on solver and clean up afterward
///
/// # Arguments
/// * `ctx` - SMT expression context
/// * `smt_ctx` - SMT solver
/// * `assumptions` - iterable set of assumptions for query
///
/// # Returns
/// [`CheckSatResponse`] with query result
///
/// # Errors
/// SMT solver crashes
fn query(
    ctx: &Context,
    smt_ctx: &mut impl SolverContext,
    assumptions: impl IntoIterator<Item = ExprRef>
) -> Result<CheckSatResponse> {
    // Run SMT query and remove SMT frame
    let smt_res = check_assuming(ctx, smt_ctx, assumptions);
    check_assuming_end(smt_ctx)?;

    // Return result
    smt_res
}

/// Construct witness from counterexample trace
///
/// # Preconditions
/// Input counterexample trace must be valid
///
/// # Arguments
/// * `ctx` - SMT expression context
/// * `sys` - Transition system information
/// * `cex_trace` - Counterexample trace
///
/// # Returns
/// Concrete [`Witness`]
fn construct_witness(
    ctx: &mut Context,
    sys: &TransitionSystem,
    cex_trace: &CexEntry
) -> Witness {
    // Result witness
    let mut wit = Witness::default();

    // Add all state names
    wit.init_names.extend(
        sys.states
            .iter()
            .map(|e| Some(ctx.get_symbol_name(e.symbol).unwrap().to_string()))
            .collect::<Vec<_>>()
    );

    // Add all input names
    wit.input_names.extend(
        sys.inputs
            .iter()
            .copied()
            .map(|e| Some(ctx.get_symbol_name(e).unwrap().to_string()))
    );

    // Add the initial states
    for (_, val) in &cex_trace.states {
        let wit_val = match val {
            Value::BitVec(bv) => InitValue::BitVec(bv.clone()),
            Value::Array(av) => {
                let indices = (0..av.num_elements())
                    .map(|i| BitVecValue::from_u64(i as u64, av.index_width()))
                    .collect();

                InitValue::Array(av.clone(), indices)
            }
        };

        wit.init.push(wit_val);
    }

    // Iterate through the counterexample trace and add input values
    let mut ptr = cex_trace.clone();

    loop {
        wit.inputs.push(
            ptr.inputs.iter().cloned().map(|(_, v)| Some(v)).collect()
        );

        // Check if next pointer is valid
        if let Some(next) = &ptr.next {
            ptr = Rc::unwrap_or_clone(next.clone());
        } else {
            break;
        }
    }

    // Now, `ptr` should be the last element in the trace
    let last = ptr;
    let mut store = SymbolValueStore::default();

    // Poll states at last entry
    for (sym, val) in last.states {
        match val {
            Value::BitVec(bv) => store.define_bv(sym, &bv),
            Value::Array(av) => store.define_array(sym, av),
        }
    }

    // Poll inputs at last entry
    for (sym, val) in last.inputs {
        match val {
            Value::BitVec(bv) => store.define_bv(sym, &bv),
            Value::Array(av) => store.define_array(sym, av),
        }
    }

    // Simulate final state and add activated bad states to witness
    for (idx, &bad_expr) in sys.bad_states.iter().enumerate() {
        if let Value::BitVec(bv) = eval_expr(ctx, &store, bad_expr) && !bv.is_zero() {
            wit.failed_safety.push(idx as u32);
        }
    }

    wit
}

// -------------------------------------------------------------------------------------------------
// Core PDR
// -------------------------------------------------------------------------------------------------

/// Functions maintained by all PDR implementations
trait Pdr {
    /// # Returns
    /// frame identifier for frontier frame
    fn frontier(&self) -> FrameId;

    /// Try to extract safety property violation at frontier frame
    /// (i.e. `SAT?[R_N /\ \neg P]`)
    ///
    /// # Arguments
    /// * `ctx` - SMT expression context
    /// * `smt_ctx` - SMT solver
    /// * `sys` - Transition system information
    /// * `enc` - Transition system encoding
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
        enc: &impl TransitionSystemEncoding
    ) -> Result<Option<Cube>>;

    /// Adds empty frame to frame trace
    fn add_frame(&mut self);

    /// Block cube in frame trace at certain frame
    ///
    /// # Arguments
    /// * `ctx` - SMT expression context
    /// * `smt_ctx` - SMT solver
    /// * `sys` - Transition system information
    /// * `enc` - Transition system encoding
    /// * `cube` - Proof obligation as a [`TimedCube`]
    ///
    /// # Returns
    /// [`Some(cex)`] counterexample trace if cube could not be blocked, or [`None`] otherwise
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
    ) -> Result<Option<CexEntry>>;

    /// Try to propagate blocked cubes in each frame to the next frame
    ///
    /// # Arguments
    /// * `smt_ctx` - SMT solver
    /// * `enc` - Transition system encoding
    ///
    /// # Returns
    /// Whether fixpoint reached
    fn propagate_blocked_cubes(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        enc: &impl TransitionSystemEncoding,
    ) -> Result<bool>;
}

/// Frame trace maintained by vanilla PDR
///
/// **Representation Invariant**: `frames.len() > 0`
struct BasePdr {
    /// Cube ID counter
    cube_id: CubeId,

    /// Map between unique ID and blocked cubes
    cubes: FxHashMap<CubeId, Cube>,

    /// Frame trace containing frames with blocked cube identifiers
    frames: Vec<Vec<CubeId>>,
}

impl BasePdr {
    /// Initialize a PDR instance
    ///
    /// # Precondition
    /// State variables in transition system need to be stepped
    /// at two adjacent steps
    ///
    /// # Arguments
    /// * `ctx` - SMT expression context
    /// * `sys` - Transition system information
    /// * `enc` - Transition system encoding
    fn init(
        ctx: &mut Context,
        sys: &TransitionSystem,
    ) -> Self {
        let mut init_cube = Cube::default();

        // Get all initial states from the system and create equalities between symbol
        // and initial values
        for state in &sys.states {
            if let Some(init) = state.init {
                let lit = ctx.equal(state.symbol, init);
                init_cube.literals.push(lit);
            }
        }

        Self {
            cube_id: 1,
            cubes: once(init_cube).map(|e| (0, e)).collect(),
            frames: vec![vec![0usize]],
        }
    }

    /// Return list of clauses for non-init frames, or list of cubes for init frame
    ///
    /// # Arguments
    /// * `ctx` - SMT expression context
    /// * `frame` - Frame identifier to yield assumptions from
    ///
    /// # Returns
    /// SMT expression representing assumptions of frame
    ///
    /// # Panics
    /// If [`FrameId::Infty`] is passed as the frame identifier
    fn frame_assumptions(&self, ctx: &mut Context, frame: FrameId) -> ExprRef {
        assert_ne!(frame, FrameId::Infty);

        frame.get_step().map_or_else(|| panic!("No infinite frame in `BasePdr`"), |step| {
            assert!(step < self.frames.len());

            if step == 0 {
                // Special case: init frame is just conjunction
                self.cubes[&0].to_expr(ctx)
            } else {
                // Else, just get conjunction of negated cubes (clauses)
                self.frames[step]
                    .iter()
                    .fold(ctx.get_true(), |acc, id| {
                        let clause = self.cubes[id].negate(ctx);
                        ctx.and(acc, clause)
                    })
            }
        })
    }

    /// Run relative inductiveness query
    /// (i.e. `SAT?[R_{i - 1} /\ \neg c /\ T c']`)
    ///
    /// # Arguments
    /// * `ctx` - SMT expression context
    /// * `smt_ctx` - SMT solver
    /// * `enc` - Transition system encoding
    /// * `cube` - [`TimedCube`] target
    /// * `query_type` - [`RelIndType`] with desired query type
    ///
    /// # Returns
    /// [`CheckSatResponse`] with query result
    fn rel_ind(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        enc: &impl TransitionSystemEncoding,
        cube: &TimedCube,
        query_type: RelIndType
    ) -> Result<CheckSatResponse> {
        // Query assumptions
        let mut assumptions = Vec::new();

        // Get frame assumption
        let frame_assumption = self.frame_assumptions(ctx, cube.frame.decrement());
        assumptions.push(expr_at_step(ctx, enc, frame_assumption, CUR_STEP));

        // Next step cube
        let cube_expr = cube.cube.to_expr(ctx);
        let cube_nxt = expr_at_step(ctx, enc, cube_expr, NXT_STEP);
        assumptions.push(cube_nxt);

        // Current step negation cube
        if query_type == RelIndType::Extended {
            let neg_cube_expr = cube.cube.negate(ctx);
            let neg_cube_cur = expr_at_step(ctx, enc, neg_cube_expr, CUR_STEP);
            assumptions.push(neg_cube_cur);
        }

        // Run SMT query
        query(ctx, smt_ctx, assumptions)
    }

    /// Run [`BasePdr::rel_ind`], but yield bit-level witness cube on `SAT` results
    ///
    /// # Arguments
    /// * `ctx` - SMT expression context
    /// * `smt_ctx` - SMT solver
    /// * `sys` - Transition system information
    /// * `enc` - Transition system encoding
    /// * `cube` - [`TimedCube`] target
    ///
    /// # Returns
    /// [`Some(cube)`] with `SAT` result, else [`None`]
    fn solve_rel(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
        enc: &impl TransitionSystemEncoding,
        cube: &TimedCube,
    ) -> Result<Option<Cube>> {
        if self.rel_ind(ctx, smt_ctx, enc, cube, RelIndType::Extended)? == CheckSatResponse::Sat {
            let wit = get_bit_level_cube(ctx, smt_ctx, sys, enc, CUR_STEP)?;
            Ok(Some(wit))
        } else {
            Ok(None)
        }
    }

    /// Check whether a cube intersects with the initial states
    /// (i.e. `SAT?[R_0 /\ c]`)
    ///
    /// # Arguments
    /// * `ctx` - SMT solver context
    /// * `smt_ctx` - SMT solver
    /// * `cube` - Cube to test
    ///
    /// # Returns
    /// Whether `cube` intersects with the initial states
    ///
    /// # Errors
    /// Return [`Error:UnexpectedResponse`] for `Unknown` SMT queries
    fn intersects_init(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        enc: &impl TransitionSystemEncoding,
        cube: &Cube
    ) -> Result<bool> {
        // Get initial states
        let init_frame = self.frame_assumptions(ctx, FrameId::Step(0));
        let init_cur = expr_at_step(ctx, enc, init_frame, CUR_STEP);

        // Assert cube at current step
        let cube_expr = cube.to_expr(ctx);
        let cube_cur = expr_at_step(ctx, enc, cube_expr, CUR_STEP);

        // Run SMT query
        match query(ctx, smt_ctx, vec![init_cur, cube_cur])? {
            CheckSatResponse::Sat => Ok(true),
            CheckSatResponse::Unsat => Ok(false),
            CheckSatResponse::Unknown => Err(
                Error::UnexpectedResponse(
                    String::from("`intersects_init`"),
                    String::from("unknown response"),
                )
            )
        }
    }

    /// Generalize a blocked cube with literal dropping
    ///
    /// # Preconditions
    /// Input cube must already be blocked at the frame
    ///
    /// # Arguments
    /// * `ctx` - SMT solver context
    /// * `smt_ctx` - SMT solver
    /// * `enc` - Transition system encoding
    /// * `cube` - [`TimedCube`] with cube to generalize and blocked frame
    ///
    /// # Returns
    /// Generalized cube
    fn generalize(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        enc: &impl TransitionSystemEncoding,
        cube: &TimedCube
    ) -> Result<Cube> {
        // Remaining, un-dropped literals
        let mut rem_lits = cube.cube.literals
            .iter()
            .enumerate()
            .collect::<FxHashMap<_, _>>();

        for idx in 0..cube.cube.literals.len() {
            // If only one literal or less remaining, exit
            if rem_lits.len() <= 1 {
                break;
            }

            // Try to drop a literal
            let mut copy_lits = rem_lits.clone();
            copy_lits.remove(&idx);

            // Create literal-dropped cube
            let lits = copy_lits
                .values()
                .copied()
                .copied()
                .collect::<Vec<_>>();
            let drop_cube = TimedCube {
                cube: Cube {
                    literals: lits,
                },
                frame: cube.frame,
            };

            // Test for initial state intersection and relative inductiveness
            if !self.intersects_init(ctx, smt_ctx, enc, &drop_cube.cube)? &&
                self.rel_ind(ctx, smt_ctx, enc, &drop_cube, RelIndType::Standard)?
                == CheckSatResponse::Unsat {
                // Check succeeded: permanently remove literal
                rem_lits.remove(&idx);
            }
        }

        // Collect all remaining literals into cube
        Ok(
            Cube {
                literals: rem_lits
                    .values()
                    .copied()
                    .copied()
                    .collect(),
            }
        )
    }

    /// Add blocked cubes to preceding frames
    ///
    /// # Preconditions
    /// Input cube must be blocked at frame and previous frames
    ///
    /// # Arguments
    /// * `ctx`: SMT expression context
    /// * `enc`: Transition system encoding
    /// * `cube` - Cube to add
    ///
    /// # Panics
    /// For cubes associated with infinite frame
    fn add_blocked_cube(
        &mut self,
        cube: &TimedCube,
    ) {
        // Get frontier index
        let front = cube.frame.get_step().unwrap();

        // Add cube to registry
        let id = self.cube_id;
        self.cubes.insert(id, cube.cube.clone());
        self.cube_id += 1;

        // Add new cube to all frames
        for idx in 1..=front {
            self.frames[idx].push(id);
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
            .map(|&b| expr_at_step(ctx, enc, b, CUR_STEP))
            .collect();

        // Disjunct all bad state literals
        let bad_expr = bad_lits
            .iter()
            .fold(ctx.get_false(), |acc, &b| ctx.or(acc, b));

        // Get frame assumptions for frontier frame
        let front_assumption = self.frame_assumptions(ctx, front);
        let front_cur = expr_at_step(ctx, enc, front_assumption, CUR_STEP);

        // Run query SAT?[R_N /\ \neg P]
        match query(ctx, smt_ctx, vec![front_cur, bad_expr])? {
            CheckSatResponse::Sat => {
                // Safety property violation found: return witness cube
                let bad_cube = get_bit_level_cube(ctx, smt_ctx, sys, enc, CUR_STEP)?;
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

    fn block_cube(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
        enc: &impl TransitionSystemEncoding,
        cube: &TimedCube
    ) -> Result<Option<CexEntry>> {
        // Min-queue of proof obligations
        let mut worklist = BinaryHeap::new();

        // Initialize counterexample trace to initial node
        let init_cex = Rc::new(CexEntry {
            states: extract_state_values(ctx, smt_ctx, sys, enc, CUR_STEP)?,
            inputs: extract_input_values(ctx, smt_ctx, sys, enc)?,
            next: None,
        });

        // Enqueue initial proof obligation
        worklist.push(Reverse(ProofObj(cube.clone(), init_cex)));

        // Try to solve all proof obligations
        while let Some(Reverse(ProofObj(obj, cex))) = worklist.pop() {
            // If initial frame reached, exit
            if obj.frame == FrameId::Step(0) {
                return Ok(Some(Rc::try_unwrap(cex).unwrap()));
            }

            if let Some(wit)  = self.solve_rel(ctx, smt_ctx, sys, enc, &obj)? {
                // Create new counterexample entry for predecessor
                let cex_entry = Rc::new(CexEntry {
                    states: extract_state_values(ctx, smt_ctx, sys, enc, CUR_STEP)?,
                    inputs: extract_input_values(ctx, smt_ctx, sys, enc)?,
                    next: Some(Rc::clone(&cex)),
                });

                // Counterexample found: try to block predecessor and current obligation
                worklist.push(
                    Reverse(
                        ProofObj(
                            TimedCube {
                                cube: wit,
                                frame: obj.frame.decrement(),
                            },
                            cex_entry,
                        )
                    )
                );
                worklist.push(Reverse(ProofObj(obj, cex)));
            } else {
                // Generalize cube
                let gen_cube = self.generalize(ctx, smt_ctx, enc, &obj)?;

                // Refine frame trace with cube
                self.add_blocked_cube(
                    &TimedCube { cube: gen_cube, frame: obj.frame, }
                );
            }
        }

        Ok(None)
    }

    fn propagate_blocked_cubes(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        enc: &impl TransitionSystemEncoding
    ) -> Result<bool> {
        // Get frame index
        let front = self.frontier().get_step().unwrap();

        // Try to propagate blocked cubes in each frame forward
        for idx in 1..front {
            let mut num_left = self.frames[idx].len();

            for id_idx in 0..self.frames[idx].len() {
                // Get cube ID
                let id = self.frames[idx][id_idx];

                // Get timed cube for relative inductiveness query
                let query_cube = TimedCube {
                    cube: self.cubes[&id].clone(),
                    frame: FrameId::Step(idx + 1),
                };

                // Check that cube is still blocked in next frame
                if self.rel_ind(ctx, smt_ctx, enc, &query_cube, RelIndType::Standard)?
                    == CheckSatResponse::Unsat {
                    // Add blocked cube to next frame
                    self.frames[idx + 1].push(id);
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

/// Runs PDR on a finite-state transition system with a safety property
///
/// # Arguments
/// * `ctx` - SMT expression context
/// * `smt_ctx` - SMT solver
/// * `sys` - Transition system information
///
/// # Returns
/// [`ModelCheckResult`] with safety property proof status
///
/// # Errors
/// SMT solver crashes
///
/// # Panics
/// SMT solver crashes
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
    enc.init_at(ctx, smt_ctx, CUR_STEP)?;
    enc.unroll(ctx, smt_ctx)?;

    // Initialize PDR
    let mut state = BasePdr::init(ctx, sys);

    // PDR loop
    while state.frontier().get_step().unwrap() + 1 < MAX_FRAMES {
        // Try to get bad cube
        let bad_cube = state.get_bad_cube(ctx, smt_ctx, sys, &enc)?;

        if let Some(bad) = bad_cube {
            // Try to block cube
            if let Some(cex) =state.block_cube(
                ctx,
                smt_ctx,
                sys,
                &enc,
                &TimedCube { cube: bad, frame: state.frontier(), })? {
                // Cube could not be blocked: construct witness and fail
                let wit = construct_witness(ctx, sys, &cex);
                return Ok(ModelCheckResult::Fail(wit));
            }
        } else {
            // Add new frame
            state.add_frame();

            // Check if inductive invariant found
            if state.propagate_blocked_cubes(ctx, smt_ctx, &enc)? {
                return Ok(ModelCheckResult::Success);
            }
        }
    }

    Ok(ModelCheckResult::Unknown)
}
