use std::path::Path;
use std::sync::Once;
use baa::{BitVecOps, Value};
use patronus::btor2;
use patronus::expr::Context;
use patronus::mc::{pdr, InitValue, ModelCheckResult, Witness};
use patronus::sim::{InitKind, Interpreter, Simulator};
use patronus::smt::{Solver, BITWUZLA};
use patronus::system::TransitionSystem;

// Test initialization
static INIT: Once = Once::new();

// Checks to see if Bitwuzla is installed on the host
fn bitwuzla_exists() -> bool {
    std::process::Command::new("bitwuzla")
        .arg("--version")
        .output()
        .is_ok()
}

// Assert that all test dependencies are satisfied
fn dep_check() {
    INIT.call_once(|| {
        assert!(bitwuzla_exists());
    });
}

// SMT output directory
const SMT_OUT: &str = "tests/patronus_out";

// Trivial circuit whose initial state violates the safety property
const TRIVIAL_FAIL: &str =  r"
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

/// Two bit counter that start from 2 and is incremented every cycle, and asserts that counter
/// register is never 0 (which is not true due to overflow)
const OVERFLOW: &str = r"
1 sort bitvec 1
2 input 1 clk ; Overflow.sv:1.23-1.26
3 sort bitvec 2
4 const 3 10
5 state 3 count
6 init 3 5 4
7 redor 1 5
8 const 1 1
9 not 1 7
10 and 1 8 9
11 bad 10 Overflow.sv:9.9-9.31
12 uext 3 8 1
13 add 3 5 12
14 next 3 5 13
";

/// Four-bit example circuit from thesis
const AMAN_GOEL_4: &str = r"
1 sort bitvec 1
2 input 1 clk
3 sort bitvec 4
4 const 3 0001
5 state 3 u
6 init 3 5 4
7 state 3 v
8 init 3 7 4
9 add 3 5 7
10 neq 1 9 4
11 const 1 1
12 not 1 10
13 and 1 11 12
14 bad 13
15 add 3 7 4
16 add 3 5 7
17 ult 1 5 7
18 ite 3 17 16 15
19 next 3 5 18
20 add 3 7 4
21 next 3 7 20
";

/// Circuit where one register starts at 0, always goes to 1, and another
/// register copies value: assert that second register is 1 when first one is 1
const DELAY: &str = r"
1 sort bitvec 1
2 input 1 clk ; Delay.sv:1.20-1.23
3 const 1 0
4 state 1 reg0
5 init 1 4 3
6 not 1 4
7 state 1 reg1
8 init 1 7 3
9 and 1 6 7
10 not 1 9
11 const 1 1
12 not 1 10
13 and 1 11 12
14 bad 13 Delay.sv:14.9-14.53
15 next 1 4 11
16 next 1 7 4
";

/// Circuit that initializes registers to different values and swaps them each cycle
/// Asserts that register values are always different
const SWAP: &str = r"
1 sort bitvec 1
2 input 1 clk ; Swap.sv:1.19-1.22
3 const 1 0
4 state 1 a
5 init 1 4 3
6 const 1 1
7 state 1 b
8 init 1 7 6
9 neq 1 4 7
10 not 1 9
11 and 1 6 10
12 bad 11 Swap.sv:13.9-13.24
13 next 1 4 7
14 next 1 7 4
";

/// Run PDR on a BTOR string and return the result
fn run_pdr_str(btor: &str, out_file: Option<&str>) -> (Context, TransitionSystem, ModelCheckResult) {
    // System initialization
    let mut ctx = Context::default();
    let sys = btor2::parse_str(&mut ctx, btor, Some("test_pdr")).expect("parse failed");

    let mut smt_ctx = out_file.map_or_else(
        || BITWUZLA.start(None).expect("solver failed"),
        |out_file| {
            // Output file
            let path = Path::new(out_file);
            if let Some(parent) = path.parent() { std::fs::create_dir_all(parent).unwrap(); }
            let file = std::fs::File::create(path).unwrap();
            BITWUZLA.start(Some(file)).expect("start failed")
        }
    );

    let res = pdr(&mut ctx, &mut smt_ctx, &sys).expect("pdr failed");
    (ctx, sys, res)
}

/// Run PDR on a BTOR file and return the result
fn run_pdr_file(btor_file: &str, out_file: Option<&str>) -> (Context, TransitionSystem, ModelCheckResult) {
    // System initialization
    let (mut ctx, sys) = btor2::parse_file(btor_file).expect("parse failed");
    let mut smt_ctx = out_file.map_or_else(
        || BITWUZLA.start(None).expect("solver failed"),
        |out_file| {
            // Output file
            let path = Path::new(out_file);
            if let Some(parent) = path.parent() { std::fs::create_dir_all(parent).unwrap(); }
            let file = std::fs::File::create(path).unwrap();
            BITWUZLA.start(Some(file)).expect("start failed")
        }
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

#[cfg(test)]
mod pdr_tests {
    use super::*;

    #[test]
    fn test_trivial_fail() {
        dep_check();

        let (ctx, sys, res) =
            run_pdr_str(TRIVIAL_FAIL, Some(format!("{SMT_OUT}/trivial_fail.smt").as_str()));

        if let ModelCheckResult::Fail(wit) = res {
            validate_witness(&ctx, &sys, &wit);
        } else {
            panic!("test_trivial_fail failed");
        }
    }

    #[test]
    fn test_trivial_input_fail() {
        dep_check();

        let (ctx, sys, res) =
            run_pdr_str(TRIGGER_BAD, Some(format!("{SMT_OUT}/trivial_input_fail.smt").as_str()));

        if let ModelCheckResult::Fail(wit) = res {
            validate_witness(&ctx, &sys, &wit);
        } else {
            panic!("test_input_fail failed");
        }
    }

    #[test]
    fn test_overflow_fail() {
        dep_check();

        let (ctx, sys, res) =
            run_pdr_str(OVERFLOW, Some(format!("{SMT_OUT}/overflow_fail.smt").as_str()));

        if let ModelCheckResult::Fail(wit) = res {
            validate_witness(&ctx, &sys, &wit);
        } else {
            panic!("test_input_fail failed");
        }
    }

    #[test]
    fn test_simple_fail() {
        dep_check();

        let (ctx, sys, res) =
            run_pdr_str(COUNT_2, Some(format!("{SMT_OUT}/simple_fail.smt").as_str()));

        if let ModelCheckResult::Fail(wit) = res {
            validate_witness(&ctx, &sys, &wit);
        } else {
            panic!("test_simple_fail failed");
        }
    }

    #[test]
    fn test_delay() {
        dep_check();

        let (_, _, res) =
            run_pdr_str(DELAY, Some(format!("{SMT_OUT}/delay.smt").as_str()));
        assert!(matches!(res, ModelCheckResult::Success));
    }

    #[test]
    fn test_swap() {
        dep_check();

        let (_, _, res) =
            run_pdr_str(SWAP, Some(format!("{SMT_OUT}/swap.smt").as_str()));
        assert!(matches!(res, ModelCheckResult::Success));
    }

    #[ignore = "Cubes are not subsumed in PDR, leading to solver explosion"]
    #[test]
    fn test_aman_goel_4bit() {
        dep_check();

        let (_, _, res) = run_pdr_str(AMAN_GOEL_4, None);
        assert!(matches!(res, ModelCheckResult::Success));
    }
}