use baa::{BitVecOps, Value};
use patronus::btor2;
use patronus::expr::Context;
use patronus::mc::{InitValue, ModelCheckResult, Witness, pdr};
use patronus::sim::{InitKind, Interpreter, Simulator};
use patronus::smt::{SmtLibSolver, Solver, solver_from_env};
use patronus::system::TransitionSystem;
use std::path::Path;

// SMT output directory
const _SMT_OUT: &str = "tests/patronus_out";

// Trivial circuit whose initial state violates the safety property
const TRIVIAL_FAIL: &str = r"
1 sort bitvec 1
2 ones 1
3 state 1
4 init 1 3 2
5 next 1 3 2
6 bad 3
";

/// 1-bit state (init 0) that copies a `trigger` input each cycle.
/// Bad when state = 1. Minimal CEX: trigger=1 at step 0 → bad at step 1.
const TRIGGER_BAD: &str = r"
1 sort bitvec 1
2 input 1 trigger
3 zero 1
4 state 1 st
5 init 1 4 3
6 next 1 4 2
7 bad 4
";

/// A 3-bit counter (no inputs) that starts at 0, increments by 1 each cycle,
/// and asserts bad when counter == 7 (0b111). CEX trace length = 7 steps.
const COUNT_2: &str = r"
1 sort bitvec 3
2 zero 1
3 state 1
4 init 1 3 2
5 one 1
6 add 1 3 5
7 next 1 3 6
8 ones 1
9 sort bitvec 1
10 eq 9 3 8
11 bad 10
";

/// Run PDR on a BTOR string and return the result
fn run_pdr_str(
    solver: &SmtLibSolver,
    btor: &str,
    out_file: Option<&str>,
) -> (Context, TransitionSystem, ModelCheckResult) {
    // System initialization
    let mut ctx = Context::default();
    let sys = btor2::parse_str(&mut ctx, btor, Some("test_pdr")).expect("parse failed");

    let mut smt_ctx = out_file.map_or_else(
        || solver.start(None).expect("solver failed"),
        |out_file| {
            // Output file
            let path = Path::new(out_file);
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent).unwrap();
            }
            let file = std::fs::File::create(path).unwrap();
            solver.start(Some(file)).expect("start failed")
        },
    );

    let res = pdr(&mut ctx, &mut smt_ctx, &sys).expect("pdr failed");
    (ctx, sys, res)
}

/// Run PDR on a BTOR file and return the result
fn run_pdr_file(
    solver: &SmtLibSolver,
    btor_file: &str,
    out_file: Option<&str>,
) -> (Context, TransitionSystem, ModelCheckResult) {
    // System initialization
    let (mut ctx, sys) = btor2::parse_file(btor_file).expect("parse failed");
    let mut smt_ctx = out_file.map_or_else(
        || solver.start(None).expect("solver failed"),
        |out_file| {
            // Output file
            let path = Path::new(out_file);
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent).unwrap();
            }
            let file = std::fs::File::create(path).unwrap();
            solver.start(Some(file)).expect("start failed")
        },
    );

    let res = pdr(&mut ctx, &mut smt_ctx, &sys).expect("pdr failed");
    (ctx, sys, res)
}

/// Check that generated witness actually forms a concrete counterexample trace
fn validate_witness(ctx: &Context, sys: &TransitionSystem, wit: &Witness) {
    assert!(
        !wit.failed_safety.is_empty(),
        "witness must name at least one failed safety property"
    );
    assert!(
        !wit.inputs.is_empty(),
        "witness must have at least one step entry"
    );

    let mut sim = Interpreter::new(ctx, sys);
    sim.init(InitKind::Zero);

    // Override initial state values with those captured by the solver.
    for (state, init_val) in sys.states.iter().zip(wit.init.iter()) {
        match init_val {
            InitValue::BitVec(bv) => sim.set(state.symbol, bv),
            InitValue::Array(_av, _) => panic!("No array support"),
            InitValue::None => {}
        }
    }

    let last_step = wit.inputs.len() - 1;
    for (step, step_inputs) in wit.inputs.iter().enumerate() {
        // Apply inputs for this step.
        for (inp_sym, inp_val) in sys.inputs.iter().zip(step_inputs.iter()) {
            match inp_val {
                Some(Value::BitVec(bv)) => sim.set(*inp_sym, bv),
                Some(Value::Array(_av)) => panic!("No array support"),
                None => {}
            }
        }

        if step == last_step {
            // At the final step, every listed bad state must be non-zero.
            for &bad_idx in &wit.failed_safety {
                let bad_expr = sys.bad_states[bad_idx as usize];
                if let Value::BitVec(bv) = sim.get(bad_expr) {
                    assert!(
                        !bv.is_zero(),
                        "bad state {bad_idx} should fire at step {step} but evaluates to 0"
                    );
                } else {
                    panic!("bad state {bad_idx} is not a bit-vector expression");
                }
            }
        } else {
            sim.step();
        }
    }
}

fn case_trivial_fail(solver: &SmtLibSolver) {
    let (ctx, sys, res) = run_pdr_str(solver, TRIVIAL_FAIL, None);

    if let ModelCheckResult::Fail(wit) = res {
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("test_trivial_fail failed");
    }
}

fn case_trivial_input_fail(solver: &SmtLibSolver) {
    let (ctx, sys, res) = run_pdr_str(solver, TRIGGER_BAD, None);

    if let ModelCheckResult::Fail(wit) = res {
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("test_input_fail failed");
    }
}

fn case_overflow_fail(solver: &SmtLibSolver) {
    let (ctx, sys, res) = run_pdr_file(solver, "../inputs/verilog_tests/Overflow.btor", None);

    if let ModelCheckResult::Fail(wit) = res {
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("test_input_fail failed");
    }
}

fn case_simple_fail(solver: &SmtLibSolver) {
    let (ctx, sys, res) = run_pdr_str(solver, COUNT_2, None);

    if let ModelCheckResult::Fail(wit) = res {
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("test_simple_fail failed");
    }
}

fn case_delay(solver: &SmtLibSolver) {
    let (_, _, res) = run_pdr_file(solver, "../inputs/verilog_tests/Delay.btor", None);
    assert!(matches!(res, ModelCheckResult::Success));
}

fn case_swap(solver: &SmtLibSolver) {
    let (_, _, res) = run_pdr_file(solver, "../inputs/verilog_tests/Swap.btor", None);
    assert!(matches!(res, ModelCheckResult::Success));
}

fn case_aman_goel_4bit(solver: &SmtLibSolver) {
    let (_, _, res) = run_pdr_file(solver, "../inputs/unittest/aman_goel_4bit.btor", None);
    assert!(matches!(res, ModelCheckResult::Success));
}

#[cfg(test)]
mod pdr {
    use super::*;

    #[test]
    fn test_trivial_fail() {
        case_trivial_fail(&solver_from_env());
    }

    #[test]
    fn test_trivial_input_fail() {
        case_trivial_input_fail(&solver_from_env());
    }

    #[test]
    fn test_overflow_fail() {
        case_overflow_fail(&solver_from_env());
    }

    #[test]
    fn test_simple_fail() {
        case_simple_fail(&solver_from_env());
    }

    #[test]
    fn test_delay() {
        case_delay(&solver_from_env());
    }

    #[test]
    fn test_swap() {
        case_swap(&solver_from_env());
    }

    #[test]
    fn test_aman_goel_4bit() {
        case_aman_goel_4bit(&solver_from_env());
    }
}
