use baa::{BitVecOps, Value};
use patronus::btor2;
use patronus::expr::Context;
use patronus::mc::{InitValue, ModelCheckResult, Witness, pdr};
use patronus::sim::{InitKind, Interpreter, Simulator};
use patronus::smt::{SmtLibSolver, Solver, SolverMetaData, solver_from_env};
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

/// Run PDR on a BTOR string and possibly return the result if solver is compatible with options
/// (e.g. YICES2 cannot be run with UNSAT cores enabled)
fn run_pdr_str(
    solver: &SmtLibSolver,
    btor: &str,
    out_file: Option<&str>,
    disable_unsat_cores: bool,
) -> Option<(Context, TransitionSystem, ModelCheckResult)> {
    if !solver.supports_get_unsat_assumptions() && !disable_unsat_cores {
        return None;
    }

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

    let res = pdr(&mut ctx, &mut smt_ctx, &sys, disable_unsat_cores).expect("pdr failed");
    Some((ctx, sys, res))
}

/// Run PDR on a BTOR file and possibly return the result if solver is compatible with options
/// (e.g. YICES2 cannot be run with UNSAT cores enabled)
fn run_pdr_file(
    solver: &SmtLibSolver,
    btor_file: &str,
    out_file: Option<&str>,
    disable_unsat_cores: bool,
) -> Option<(Context, TransitionSystem, ModelCheckResult)> {
    if !solver.supports_get_unsat_assumptions() && !disable_unsat_cores {
        return None;
    }

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

    let res = pdr(&mut ctx, &mut smt_ctx, &sys, disable_unsat_cores).expect("pdr failed");
    Some((ctx, sys, res))
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
    let Some((ctx, sys, res)) = run_pdr_str(solver, TRIVIAL_FAIL, None, false) else {
        return;
    };

    if let ModelCheckResult::Fail(wit) = res {
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("test_trivial_fail failed");
    }
}

fn case_trivial_fail_no_gen(solver: &SmtLibSolver) {
    let (ctx, sys, res) = run_pdr_str(solver, TRIVIAL_FAIL, None, true).unwrap();

    if let ModelCheckResult::Fail(wit) = res {
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("test_trivial_fail_no_gen failed");
    }
}

fn case_trivial_input_fail(solver: &SmtLibSolver) {
    let Some((ctx, sys, res)) = run_pdr_str(solver, TRIGGER_BAD, None, false) else {
        return;
    };

    if let ModelCheckResult::Fail(wit) = res {
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("test_input_fail failed");
    }
}

fn case_trivial_input_fail_no_gen(solver: &SmtLibSolver) {
    let (ctx, sys, res) = run_pdr_str(solver, TRIGGER_BAD, None, true).unwrap();

    if let ModelCheckResult::Fail(wit) = res {
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("test_input_fail_no_gen failed");
    }
}

fn case_overflow_fail(solver: &SmtLibSolver) {
    let Some((ctx, sys, res)) =
        run_pdr_file(solver, "../inputs/verilog_tests/Overflow.btor", None, false)
    else {
        return;
    };

    if let ModelCheckResult::Fail(wit) = res {
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("test_overflow_fail failed");
    }
}

fn case_overflow_fail_no_gen(solver: &SmtLibSolver) {
    let (ctx, sys, res) =
        run_pdr_file(solver, "../inputs/verilog_tests/Overflow.btor", None, true).unwrap();

    if let ModelCheckResult::Fail(wit) = res {
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("test_overflow_fail_no_gen failed");
    }
}

fn case_simple_fail(solver: &SmtLibSolver) {
    let Some((ctx, sys, res)) = run_pdr_str(solver, COUNT_2, None, false) else {
        return;
    };

    if let ModelCheckResult::Fail(wit) = res {
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("test_simple_fail failed");
    }
}

fn case_simple_fail_no_gen(solver: &SmtLibSolver) {
    let (ctx, sys, res) = run_pdr_str(solver, COUNT_2, None, true).unwrap();

    if let ModelCheckResult::Fail(wit) = res {
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("test_simple_fail_no_gen failed");
    }
}

fn case_quiz1_sat(solver: &SmtLibSolver) {
    let Some((ctx, sys, res)) =
        run_pdr_file(solver, "../inputs/chiseltest/Quiz1.btor", None, false)
    else {
        return;
    };

    if let ModelCheckResult::Fail(wit) = res {
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("test_quiz1_sat failed");
    }
}

fn case_quiz2_sat(solver: &SmtLibSolver) {
    let Some((ctx, sys, res)) =
        run_pdr_file(solver, "../inputs/chiseltest/Quiz2.sat.btor", None, false)
    else {
        return;
    };

    if let ModelCheckResult::Fail(wit) = res {
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("test_quiz2_sat failed");
    }
}

fn case_quiz4_sat(solver: &SmtLibSolver) {
    let Some((ctx, sys, res)) =
        run_pdr_file(solver, "../inputs/chiseltest/Quiz4.sat.btor", None, false)
    else {
        return;
    };

    if let ModelCheckResult::Fail(wit) = res {
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("test_quiz4_sat failed");
    }
}

fn case_dangling(solver: &SmtLibSolver) {
    let Some((ctx, sys, res)) =
        run_pdr_file(solver, "../inputs/unittest/dangling.btor2", None, false)
    else {
        return;
    };

    if let ModelCheckResult::Fail(wit) = res {
        validate_witness(&ctx, &sys, &wit);
    } else {
        panic!("test_dangling failed");
    }
}

fn case_delay(solver: &SmtLibSolver) {
    let Some((_, _, res)) = run_pdr_file(solver, "../inputs/verilog_tests/Delay.btor", None, false)
    else {
        return;
    };
    assert!(matches!(res, ModelCheckResult::Success));
}

fn case_delay_no_gen(solver: &SmtLibSolver) {
    let (_, _, res) =
        run_pdr_file(solver, "../inputs/verilog_tests/Delay.btor", None, true).unwrap();
    assert!(matches!(res, ModelCheckResult::Success));
}

fn case_swap(solver: &SmtLibSolver) {
    let Some((_, _, res)) = run_pdr_file(solver, "../inputs/verilog_tests/Swap.btor", None, false)
    else {
        return;
    };
    assert!(matches!(res, ModelCheckResult::Success));
}

fn case_swap_no_gen(solver: &SmtLibSolver) {
    let (_, _, res) =
        run_pdr_file(solver, "../inputs/verilog_tests/Swap.btor", None, true).unwrap();
    assert!(matches!(res, ModelCheckResult::Success));
}

fn case_aman_goel_4bit(solver: &SmtLibSolver) {
    let Some((_, _, res)) = run_pdr_file(
        solver,
        "../inputs/unittest/aman_goel_4bit.btor",
        None,
        false,
    ) else {
        return;
    };
    assert!(matches!(res, ModelCheckResult::Success));
}

fn case_aman_goel_16bit(solver: &SmtLibSolver) {
    let Some((_, _, res)) = run_pdr_file(
        solver,
        "../inputs/unittest/aman_goel_16bit.btor",
        None,
        false,
    ) else {
        return;
    };
    assert!(matches!(res, ModelCheckResult::Success));
}

fn case_quiz1_unsat(solver: &SmtLibSolver) {
    let Some((_, _, res)) =
        run_pdr_file(solver, "../inputs/chiseltest/Quiz1.unsat.btor", None, false)
    else {
        return;
    };
    assert!(matches!(res, ModelCheckResult::Success));
}

fn case_quiz2_unsat(solver: &SmtLibSolver) {
    let Some((_, _, res)) =
        run_pdr_file(solver, "../inputs/chiseltest/Quiz2.unsat.btor", None, false)
    else {
        return;
    };
    assert!(matches!(res, ModelCheckResult::Success));
}

fn case_quiz4_unsat(solver: &SmtLibSolver) {
    let Some((_, _, res)) =
        run_pdr_file(solver, "../inputs/chiseltest/Quiz4.unsat.btor", None, false)
    else {
        return;
    };
    assert!(matches!(res, ModelCheckResult::Success));
}

fn case_simple_mac(solver: &SmtLibSolver) {
    let Some((_, _, res)) = run_pdr_file(
        solver,
        "../inputs/unittest/simple_MAC_no_stall.btor2",
        None,
        false,
    ) else {
        return;
    };
    assert!(matches!(res, ModelCheckResult::Success));
}

fn case_pipe(solver: &SmtLibSolver) {
    let Some((_, _, res)) = run_pdr_file(
        solver,
        "../inputs/unittest/pipe-no-stall.btor2",
        None,
        false,
    ) else {
        return;
    };
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
    fn test_trivial_fail_no_gen() {
        case_trivial_fail_no_gen(&solver_from_env());
    }

    #[test]
    fn test_trivial_input_fail() {
        case_trivial_input_fail(&solver_from_env());
    }

    #[test]
    fn test_trivial_input_fail_no_gen() {
        case_trivial_input_fail_no_gen(&solver_from_env());
    }

    #[test]
    fn test_overflow_fail() {
        case_overflow_fail(&solver_from_env());
    }

    #[test]
    fn test_overflow_fail_no_gen() {
        case_overflow_fail_no_gen(&solver_from_env());
    }

    #[test]
    fn test_simple_fail() {
        case_simple_fail(&solver_from_env());
    }

    #[test]
    fn test_simple_fail_no_gen() {
        case_simple_fail_no_gen(&solver_from_env());
    }

    #[test]
    fn test_quiz1_sat() {
        case_quiz1_sat(&solver_from_env());
    }

    #[test]
    fn test_quiz2_sat() {
        case_quiz2_sat(&solver_from_env());
    }

    #[test]
    fn test_quiz4_sat() {
        case_quiz4_sat(&solver_from_env());
    }

    #[test]
    fn test_dangling() {
        case_dangling(&solver_from_env());
    }

    #[test]
    fn test_delay() {
        case_delay(&solver_from_env());
    }

    #[test]
    fn test_delay_no_gen() {
        case_delay_no_gen(&solver_from_env());
    }

    #[test]
    fn test_swap() {
        case_swap(&solver_from_env());
    }

    #[test]
    fn test_swap_no_gen() {
        case_swap_no_gen(&solver_from_env());
    }

    #[test]
    fn test_aman_goel_4bit() {
        case_aman_goel_4bit(&solver_from_env());
    }

    #[ignore = "need more blocked cube generalization"]
    #[test]
    fn test_aman_goel_16bit() {
        case_aman_goel_16bit(&solver_from_env());
    }

    #[test]
    fn test_quiz1_unsat() {
        case_quiz1_unsat(&solver_from_env());
    }

    #[test]
    fn test_quiz2_unsat() {
        case_quiz2_unsat(&solver_from_env());
    }

    #[test]
    fn test_quiz4_unsat() {
        case_quiz4_unsat(&solver_from_env());
    }

    #[test]
    fn test_simple_mac() {
        case_simple_mac(&solver_from_env());
    }

    #[test]
    fn test_pipe() {
        case_pipe(&solver_from_env());
    }
}
