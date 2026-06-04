// Copyright 2024-2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use std::cmp::{Ordering, Reverse};
use std::collections::BinaryHeap;
use baa::{ArrayOps, BitVecOps, BitVecValue, Value};
use rustc_hash::{FxHashMap, FxHashSet};
use crate::mc::bmc::TransitionSystemEncoding;
use crate::expr::*;
use crate::mc::{check_assuming, get_smt_value, InitValue, ModelCheckResult, Witness};
use crate::mc::bmc::start_bmc_or_pdr;
use crate::smt::*;
use crate::system::TransitionSystem;

type Result<T> = crate::smt::Result<T>;
type CubeId = usize;
type Step = u64;
type CexChain = Vec<CexEntry>;

const CUR_STEP: Step = 1; // Current state constant
const NXT_STEP: Step = 2; // Next state constant
const MAX_FRAMES: usize = 1000; // Maximum number of frames allowed by PDR

// ------------------------------------------------------------------------------------------------
// Core PDR data structures
// ------------------------------------------------------------------------------------------------

/// `Formula` specifies methods on SMT logic formulas
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

impl Formula for Cube {
    fn to_expr(&self, ctx: &mut Context) -> ExprRef {
        self.literals
            .iter()
            .copied()
            .fold(ctx.get_true(), |acc, e| ctx.and(acc, e))
    }

    fn negate(&self, ctx: &mut Context) -> ExprRef {
        self.literals
            .iter()
            .copied()
            .fold(
                ctx.get_false(),
                |acc, e| {
                    let neg_lit = ctx.not(e);
                    ctx.or(acc, neg_lit)
                }
            )
    }
}

/// `TimedCube` is composed of a cube and a frame to block it at
#[derive(Debug, Default, Clone)]
struct TimedCube {
    cube: Cube, // Contained cube
    frame: usize, // Frame to block at
}

// Custom comparators for `TimedCube`
impl Eq for TimedCube {}
impl PartialEq for TimedCube {
    fn eq(&self, other: &Self) -> bool {
        self.frame.eq(&other.frame)
    }
}
impl PartialOrd for TimedCube {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for TimedCube {
    fn cmp(&self, other: &Self) -> Ordering {
        self.frame.cmp(&other.frame)
    }
}

/// `BlockedCube` contains the activation literal and original cube for a cube blocked by PDR
#[derive(Debug, Clone)]
struct BlockedCube {
    act: ExprRef,
    cube: Cube,
}

/// `CexEntry` is a node in a counterexample trace
#[derive(Debug, Clone)]
struct CexEntry {
    state_values: Vec<Value>,
    inputs: Vec<Value>,
}

// ------------------------------------------------------------------------------------------------
// PDR helper functions
// ------------------------------------------------------------------------------------------------

/// Convert an SMT expression to its stepped version
fn expr_at_step(
   ctx: &mut Context,
   enc: &impl TransitionSystemEncoding,
   expr: ExprRef,
   step: Step
) -> ExprRef {
   simple_transform_expr(
       ctx,
       expr,
       |ctx, e, _| {
           if ctx[e].is_symbol() {
               Some(enc.get_at(ctx, e, step))
           } else {
               None
           }
       }
   )
}

/// Check if a cube syntactically subsumes another cube
/// (i.e. `c_q \subseteq c_b`, where `c_a` and `c_b` are cubes with sets of literals)
fn subsumes(a: &Cube, b: &Cube) -> bool {
    // Get set of literals
    let lit_set: FxHashSet<ExprRef> =
        b.literals.iter().copied().collect();

    // Check that all `a` literals exist in `b`
    a.literals
        .iter()
        .all(|e| lit_set.contains(e))
}

/// Extract state values of the system at a certain step
fn extract_state_values(
   ctx: &mut Context,
   smt_ctx: &mut impl SolverContext,
   sys: &TransitionSystem,
   enc: &impl TransitionSystemEncoding,
   step: Step
) -> Result<Vec<Value>> {
    let mut state_values = Vec::with_capacity(sys.states.len());

    for state in &sys.states {
        let sym = enc.get_at(ctx, state.symbol, step);
        state_values.push(get_smt_value(ctx, smt_ctx, sym)?);
    }

    Ok(state_values)
}

/// Extract input values of the system at a certain step
fn extract_input_values(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
    enc: &impl TransitionSystemEncoding,
    step: Step
) -> Result<Vec<Value>> {
    let mut input_values = Vec::with_capacity(sys.inputs.len());

    for &input in &sys.inputs {
        let sym = enc.get_at(ctx, input, step);
        input_values.push(get_smt_value(ctx, smt_ctx, sym)?);
    }

    Ok(input_values)
}

/// Extract bitvectors from solver as bit-level cubes
///
/// TODO: Add array support
fn get_bit_level_cube(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
    enc: &impl TransitionSystemEncoding,
    step: Step
) -> Result<Cube> {
    let mut literals = Vec::new();

    // Get values associated with states
    let vals = extract_state_values(ctx, smt_ctx, sys, enc, step)?;

    debug_assert_eq!(vals.len(), sys.states.len());

    for (state, val) in sys.states.iter().zip(vals.iter()) {
        match val {
            Value::BitVec(bv) => {
                // Bit vector width
                let width = bv.width();

                // Iterate through all bits of the bitvector
                for idx in 0..width {
                    // Get value of bit
                    let bit = ctx.slice(state.symbol, idx, idx);
                    let bit_val = if bv.is_bit_set(idx) { ctx.get_true() }
                                            else { ctx.get_false() };

                    // Set equality and add to list of literals
                    let literal = ctx.equal(bit, bit_val);
                    literals.push(literal);
                }
            },
            Value::Array(av) => {
               todo!("Finish implementation") // TODO: Focus on getting the relevant indices
            },
        }
    }

    Ok(Cube { literals })
}

/// Constructs a witness from a counterexample trace
///
/// **Requires**: the first step of the trace be the initial state
/// and the last step of the trace be a bad state
fn construct_witness(
    ctx: &Context,
    sys: &TransitionSystem,
    cex_chain: &CexChain,
) -> Witness {
    assert!(!cex_chain.is_empty());

    // Resulting witness
    let mut witness = Witness::default();

    // Add all state names
    for state in &sys.states {
        witness.init_names
            .push(Some(ctx.get_symbol_name(state.symbol).unwrap().to_string()));
    }

    // Add all input names
    for &input in &sys.inputs {
        witness.input_names
            .push(Some(ctx.get_symbol_name(input).unwrap().to_string()));
    }

    // Initial state is first entry of trace
    let first_entry = cex_chain.first().unwrap();

    // Add the initial states
    for val in &first_entry.state_values {
        // Map witness value to an init BitVec or Array
        let wit_val = match val {
            Value::BitVec(v) => InitValue::BitVec(v.clone()),
            Value::Array(v) => {
                let indices = (0..v.num_elements())
                    .map(|i| BitVecValue::from_u64(i as u64, v.index_width()))
                    .collect();

                InitValue::Array(v.clone(), indices)
            },
        };

        // Add to initial value list
        witness.init.push(wit_val);
    }

    // Iterate through the CEX chain and add input values to witness
    for entry in cex_chain {
        witness.inputs
            .push(entry.inputs.iter().cloned().map(Some).collect());
    }

    // Last entry of CEX chain must be a bad state (by assumption)
    let last_entry = cex_chain.last().unwrap();
    let mut store = SymbolValueStore::default();

    assert_eq!(last_entry.state_values.len(), sys.states.len());
    assert_eq!(last_entry.inputs.len(), sys.inputs.len());

    // Define relevant states
    for (state, val) in sys.states.iter().zip(last_entry.state_values.iter()) {
        match val {
            Value::BitVec(bv) => store.define_bv(state.symbol, bv),
            Value::Array(av) => store.define_array(state.symbol, av.clone()),
        }
    }

    // Define relevant inputs
    for (input, val) in sys.inputs.iter().zip(last_entry.inputs.iter()) {
        match val {
            Value::BitVec(bv) => store.define_bv(*input, bv),
            Value::Array(av) => store.define_array(*input, av.clone()),
        }
    }

    // Simulate final state and add activated bad states
    for (idx, &bad_expr) in sys.bad_states.iter().enumerate() {
        if let Value::BitVec(bv) = eval_expr(ctx, &store, bad_expr) && !bv.is_zero() {
            witness.failed_safety.push(idx as u32);
        }
    }

    witness
}

// ------------------------------------------------------------------------------------------------
// Main PDR state and subroutines
// ------------------------------------------------------------------------------------------------

/// `PdrState` is the frames accumulated by PDR
///
/// **Representation Invariant**: `frames` must always have length >= 2,
/// where the first frame is the initial frame and the last frame is the
/// infinite frame
struct PdrState {
    act_counter: u64,
    cubes: FxHashMap<CubeId, BlockedCube>, // Collection of activation literals for blocked cubes
    frames: Vec<Vec<CubeId>>, // Delta trace of clauses in each frame
}

impl PdrState {
    fn init(
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
        enc: &impl TransitionSystemEncoding
    ) -> Result<Self> {
        // Get an activation literal for the initial state
        let init_act = ctx.bv_symbol("act_0", 1);
        let mut init_cube = Cube::default();

        // Poll all initial states from the system
        for state in &sys.states {
            if let Some(init) = state.init {
                let sym = enc.get_at(ctx, state.symbol, CUR_STEP);
                let lit = ctx.equal(sym, init);
                init_cube.literals.push(lit);
            }
        }

        // Assert activation literal in solver
        let cube_expr = init_cube.to_expr(ctx);
        let imp = ctx.implies(init_act, cube_expr);
        smt_ctx.declare_const(ctx, init_act)?;
        smt_ctx.assert(ctx, imp)?;

        // Return initialized PDR state
        Ok(Self {
            act_counter: 1u64,
            cubes: std::iter::once(BlockedCube {
                    act: init_act,
                    cube: init_cube,
                }).map(|e| (0, e)).collect(),
            frames: vec![vec![0usize], vec![]],
        })
    }

    /// Returns the number of finite-range (relatively-inductive) frames
    #[inline]
    const fn depth(&self) -> usize {
        self.frames.len() - 1
    }

    /// Add an empty frame
    fn add_frame(&mut self) {
        self.frames.insert(self.depth(), Vec::new());
    }

    /// Return all clauses activation literals associated with a frame
    fn frame_assumptions(&self, frame_idx: usize) -> Vec<ExprRef> {
        let mut act_literals = Vec::new();

        // Always add initial activation literal (to prevent intersection with initial state)
        act_literals.push(self.cubes[&0].act);

        // Also reads the last infinite frame
        for idx in frame_idx..=self.depth() {
            // Push activation literals from this frame into collection
            act_literals.extend(
                self.frames[idx]
                    .iter()
                    .map(|id| self.cubes[id].act)
            );
        }

        act_literals
    }

    /// Find a bad cube based on assertion of frontier frame
    fn get_bad_cube(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
        enc: &impl TransitionSystemEncoding
    ) -> Result<Option<Cube>> {
        // Get current frontier frame index
        let front_idx = self.depth() - 1;

        // Bad states
        let bad_states : Vec<ExprRef> =
            sys.bad_states
                .iter()
                .map(|b| enc.get_at(ctx, *b, NXT_STEP))
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
            CheckSatResponse::Sat => {
                let bad_cube = get_bit_level_cube(ctx, smt_ctx, sys, enc, CUR_STEP)?;
                Ok(Some(bad_cube))
            },
            CheckSatResponse::Unsat => Ok(None),
            CheckSatResponse::Unknown => Err(
                Error::UnexpectedResponse(
                    String::from("`get_bad_cube`"),
                    String::from("unknown"),
                )
            ),
        }
    }

    /// Check whether cube intersects with initial state
    fn init_check(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        enc: &impl TransitionSystemEncoding,
        cube: &Cube
    ) -> Result<CheckSatResponse> {
        // Assert the initial frame
        let mut assumptions = self.frame_assumptions(0);

        // Assert the cube holds
        let cube_expr = cube.to_expr(ctx);
        let cube_expr = expr_at_step(ctx, enc, cube_expr, CUR_STEP);
        assumptions.push(cube_expr);

        check_assuming(ctx, smt_ctx, assumptions)
    }

    /// Check for relative inductiveness by running the SMT query `SAT?[F_k /\ \neg c /\ T /\ c']`,
    /// where `F_k` is the relative frame, `c` is a cube, `c'` is the next state cube, and
    /// `T` is the transition relation
    ///
    /// **Checks**: relative inductive check is not evaluated against initial frame
    ///             (Use `init_check` for initial state overlap test)
    ///
    /// Returns a `CheckSatResponse` with the query result
    fn rel_ind_check(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        enc: &impl TransitionSystemEncoding,
        proof_obj: &TimedCube
    ) -> Result<CheckSatResponse> {
        // Check for initial frame violation
        assert_ne!(proof_obj.frame, 0);

        // Start with frame assumptions
        let mut assumptions = self.frame_assumptions(proof_obj.frame);

        // Yield relevant cube expressions
        let cube_expr = proof_obj.cube.to_expr(ctx);
        let neg_cube_expr = proof_obj.cube.negate(ctx);

        // Only add assertion for `c` in the next step if not relative to the initial frame
        assumptions.push(
            expr_at_step(
                ctx,
                enc,
                neg_cube_expr,
                CUR_STEP
            )
        );
        assumptions.push(
            expr_at_step(
                ctx,
                enc,
                cube_expr,
                NXT_STEP
            )
        );

        check_assuming(ctx, smt_ctx, assumptions)
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
        proof_obj: &TimedCube
    ) -> Result<Option<Cube>> {
        // Perform relative inductiveness check
        match self.rel_ind_check(ctx, smt_ctx, enc, proof_obj)? {
            CheckSatResponse::Sat => {
                let bad_cube = get_bit_level_cube(ctx, smt_ctx, sys, enc, CUR_STEP)?;
                Ok(Some(bad_cube))
            },
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
        enc: &impl TransitionSystemEncoding,
        proof_obj: &TimedCube
    ) -> Result<Cube> {
        // Remaining literals from generalization
        let mut rem_literals = proof_obj.cube.literals
            .iter()
            .enumerate()
            .collect::<FxHashMap<_, _>>();

        for idx in 0..proof_obj.cube.literals.len() {
            // If only one literal remaining, do not try to drop
            if rem_literals.len() <= 1 {
                break;
            }

            // Drop literal
            let rem_expr = rem_literals.remove(&idx).unwrap();

            // Collect remaining literals
            let literals = rem_literals
                .values()
                .map(|e| **e)
                .collect();

            // Create updated proof obligation
            let test_obj = TimedCube {
                cube: Cube { literals },
                frame: proof_obj.frame,
            };

            // Check if literal-dropped cube is still blocked by frame
            match self.rel_ind_check(ctx, smt_ctx, enc, &test_obj)? {
                CheckSatResponse::Sat | CheckSatResponse::Unknown => {
                    rem_literals.insert(idx, rem_expr);
                }, // Unable to drop literal: restore state
                CheckSatResponse::Unsat => (), // Able to drop literal
            }
        }

        // Create new cube with unsuccessfully dropped literals
        Ok(Cube { literals: rem_literals.values().map(|e| **e).collect() })
    }


    /// Add blocked clause to frames
    fn add_blocked_cube(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        enc: &impl TransitionSystemEncoding,
        blocked_cube: &TimedCube
    ) -> Result<()> {
        // Create clause from blocked cube
        let clause = blocked_cube.cube.negate(&mut *ctx);

        // Cube ID
        let id = self.act_counter;
        self.act_counter += 1;

        // Go through each frame and remove subsumed cubes
        for idx in 1..=blocked_cube.frame {
            // Remove all subsumed cubes
            let cleaned_frame: Vec<CubeId> =
                self.frames[idx]
                    .iter()
                    .filter(
                        |c| !subsumes(&blocked_cube.cube, &self.cubes.get(*c).unwrap().cube)
                    )
                    .copied()
                    .collect();

            // Replace frame
            self.frames[idx] = cleaned_frame;
        }

        // Create new activation literal for blocked cube
        let act = ctx.bv_symbol(format!("act_{id}").as_str(), 1);
        smt_ctx.declare_const(ctx, act)?;

        // Add blocked cube to frontier frame
        self.frames[blocked_cube.frame].push(id as usize);
        self.cubes.insert(
            id as CubeId,
            BlockedCube { act, cube: blocked_cube.clone().cube, }
        );

        // Assert the new negated cube (clause) in the solver with the activation literal
        let clause_exp = expr_at_step(ctx, enc, clause, CUR_STEP);
        let imp = ctx.implies(act, clause_exp);
        smt_ctx.assert(ctx, imp)
    }

    /// Try to block bad cube
    ///
    /// Returns `None`, or a counterexample trace if cube could not be blocked
    fn block_cube(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        sys: &TransitionSystem,
        enc: &impl TransitionSystemEncoding,
        cube: &Cube
    ) -> Result<Option<CexChain>> {
        // Min-queue for proof obligations
        let mut worklist = BinaryHeap::new();

        // Counterexample trace
        let mut cex_chain = CexChain::new();

        // Add first proof obligation (try to block at frontier frame)
        worklist.push(
            Reverse(
                TimedCube {
                    cube: cube.clone(),
                    frame: self.depth() - 1,
                }
            )
        );

        // Iterate through proof obligations
        while let Some(Reverse(proof_obj)) = worklist.pop() {
            // Special case: reached initial frame
            if proof_obj.frame == 0 {
                match self.init_check(ctx, smt_ctx, enc, &proof_obj.cube)? {
                    CheckSatResponse::Sat => {
                        // Push initial state CEX entry
                        cex_chain.push(
                            CexEntry {
                                state_values: extract_state_values(ctx, smt_ctx, sys, enc, CUR_STEP)?,
                                inputs: extract_input_values(ctx, smt_ctx, sys, enc, CUR_STEP)?,
                            }
                        );

                        // Reverse chain to restore order
                        return Ok(Some(cex_chain.iter().rev().cloned().collect()));
                    },
                    CheckSatResponse::Unsat => continue,
                    CheckSatResponse::Unknown => return Err(Error::UnexpectedResponse(
                        String::from("`block_cube`"),
                        String::from("unknown result at critical step"),
                    ))
                }
            }

            if let Some(wit) = self.solve_relative(&mut *ctx, &mut *smt_ctx, sys, enc, &proof_obj)? {
                // Cube was unable to be blocked: create new proof obligations
               worklist.push(Reverse(
                    TimedCube {
                        cube: wit,
                        frame: proof_obj.frame - 1,
                    }
                ));
                worklist.push(Reverse(proof_obj));

                // Prepend new counterexample entry
                cex_chain.push(CexEntry {
                    state_values: extract_state_values(ctx, smt_ctx, sys, enc, NXT_STEP)?,
                    inputs: extract_input_values(ctx, smt_ctx, sys, enc, NXT_STEP)?,
                });
            } else {
                // Cube was blocked by frame: generalize and add to frames
                let gen_cube = { self.generalize(&mut *ctx, &mut *smt_ctx, enc, &proof_obj)? };

                let mut gen_obj = TimedCube {
                    cube : gen_cube,
                    frame: proof_obj.frame,
                };

                // Push generalized cube to the farthest possible frame
                while gen_obj.frame < self.depth() {
                    match self.rel_ind_check(&mut *ctx, &mut *smt_ctx, enc, &gen_obj)? {
                        // Relative inductiveness check fails: cannot move forward
                        CheckSatResponse::Sat | CheckSatResponse::Unknown => {
                            gen_obj.frame -= 1;
                            break;
                        },
                        // Relative inductiveness check succeeds: try next frame
                        CheckSatResponse::Unsat => gen_obj.frame += 1,
                   }
                }

                // Add blocked cube to frame
               self.add_blocked_cube(&mut *ctx, &mut *smt_ctx, enc, &gen_obj)?;
            }
        }

        Ok(None)
    }

    /// Try to propagate all frame clauses to the next frame
    ///
    /// Returns whether Fixpoint reached (therefore signaling the termination of the algorithm)
    fn propagate_blocked_cubes(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        enc: &impl TransitionSystemEncoding
    ) -> Result<bool> {
        // Iterate through all frames before the last
        for idx in 1..(self.depth() - 1) {
            // Cubes that remain in this frame
            let mut rem_cubes = Vec::new();

            // Iterate through all blocked cubes
            for id_idx in 0..self.frames[idx].len() {
                // Current cube ID
                let id = self.frames[idx][id_idx];

                // Try to block the clause in the next frame
                if self.rel_ind_check(
                    ctx,
                    smt_ctx,
                    enc,
                    &TimedCube {
                        cube: self.cubes[&id].cube.clone(),
                        frame: idx + 1,
                    }
                )? == CheckSatResponse::Unsat {
                    self.frames[idx + 1].push(id);
                } else {
                    rem_cubes.push(id);
                }
            }

            // Replace this frame with the remaining cubes
            self.frames[idx] = rem_cubes;

            // If all blocked cubes moved, inductive invariant found
            if self.frames[idx].is_empty() {
                return Ok(true);
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

    // TODO: Deal with constraints
    assert!(sys.constraints.is_empty());

    // Initialize system with current state and next state variables
    enc.init_at(ctx, smt_ctx, CUR_STEP)?;
    enc.unroll(ctx, smt_ctx)?;

    // Create PDR instance
    let mut state = PdrState::init(ctx, smt_ctx, sys, &enc)?;

    // Main PDR loop
    for _ in 0..MAX_FRAMES {
        // Extract bad cube
        let bad_cube = state.get_bad_cube(ctx, smt_ctx, sys, &enc)?;

        if let Some(bad_cube) = bad_cube {
            // Bad cube found: block the bad cube
            if let Some(cex_chain) = state.block_cube(ctx, smt_ctx, sys, &enc, &bad_cube)? {
                let wit = construct_witness(ctx, sys, &cex_chain);
                return Ok(ModelCheckResult::Fail(wit));
            }
        }
        else {
            // No bad cube found: try to find inductive invariant
            state.add_frame();

            if state.propagate_blocked_cubes(ctx, smt_ctx, &enc)? {
                // Inductive invariant holds: success
                return Ok(ModelCheckResult::Success);
            }
        }
    }

    Ok(ModelCheckResult::Unknown)
}
