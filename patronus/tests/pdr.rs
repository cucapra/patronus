use std::path::Path;
use std::sync::Once;
use patronus::btor2;
use patronus::expr::Context;
use patronus::mc::{pdr, ModelCheckResult};
use patronus::smt::{Solver, BITWUZLA};

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

/// 4-bit downscale of `inputs/unittest/aman_goel.btor` (AVR figure 1, Goel & Sakallah).
/// Two registers start equal (u = v = 1) and step together (v' = v+1;
/// u' = u<v ? u+v : v+1), so the reachable states are the diagonal u == v and
/// u+v is always even; bad = (u+v == 1) is unreachable. The inductive invariant
/// PDR must discover is u == v (mutually inductive bit-pair clauses), which makes
/// this a generalization stress test. The 16-bit original (`test_aman_goel`) needs
/// predecessor shrinking / core-based generalization to converge in reasonable time.
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

/// Run PDR on a BTOR string and return the result
fn run_pdr_str(btor: &str, out_file: Option<&str>) -> ModelCheckResult {
    // System initialization
    let mut ctx = Context::default();
    let sys = btor2::parse_str(&mut ctx, btor, Some("test_pdr")).expect("parse failed");

    let mut smt_ctx = out_file.map_or_else(
        || BITWUZLA.start(None).expect("solver failed"),
        |out_file| {
            // Output file
            let path = Path::new(out_file);
            let file = std::fs::File::create(path).unwrap();
            BITWUZLA.start(Some(file)).expect("start failed")
        }
    );

    pdr(&mut ctx, &mut smt_ctx, &sys).expect("pdr failed")
}

/// Run PDR on a BTOR file and return the result
fn run_pdr_file(btor_file: &str, out_file: Option<&str>) -> ModelCheckResult {
    // System initialization
    let (mut ctx, sys) = btor2::parse_file(btor_file).expect("parse failed");
    let mut smt_ctx = out_file.map_or_else(
        || BITWUZLA.start(None).expect("solver failed"),
        |out_file| {
            // Output file
            let path = Path::new(out_file);
            let file = std::fs::File::create(path).unwrap();
            BITWUZLA.start(Some(file)).expect("start failed")
        }
    );

    pdr(&mut ctx, &mut smt_ctx, &sys).expect("pdr failed")
}

#[cfg(test)]
mod pdr_tests {
    use super::*;

    #[test]
    fn test_trivial_fail() {
        dep_check();
        assert!(
            matches!(
                run_pdr_str(TRIVIAL_FAIL, Some(format!("{SMT_OUT}/trivial_fail.smt2").as_str())),
                ModelCheckResult::Fail(_)
            )
        );
    }

    #[test]
    fn test_trivial_input_fail() {
        dep_check();
        assert!(
            matches!(
                run_pdr_str(TRIGGER_BAD, Some(format!("{SMT_OUT}/trivial_input_fail.smt2").as_str())),
                ModelCheckResult::Fail(_)
            )
        );
    }

    #[test]
    fn test_simple_fail() {
        dep_check();
        assert!(
            matches!(
                run_pdr_str(COUNT_2, Some(format!("{SMT_OUT}/simple_fail.smt2").as_str())),
                ModelCheckResult::Fail(_)
            )
        );
    }

    #[test]
    fn test_delay_success() {
        dep_check();
        assert!(
            matches!(
                run_pdr_file("../inputs/unittest/delay.btor", Some(format!("{SMT_OUT}/delay.smt2").as_str())),
                ModelCheckResult::Success
            )
        );
    }

    #[test]
    fn test_swap_success() {
        dep_check();
        assert!(
            matches!(
                run_pdr_file("../inputs/unittest/swap.btor", Some(format!("{SMT_OUT}/swap.smt2").as_str())),
                ModelCheckResult::Success
            )
        );
    }

    #[test]
    fn test_aman_goel_4bit() {
        dep_check();
        assert!(
            matches!(
                run_pdr_str(AMAN_GOEL_4, Some(format!("{SMT_OUT}/aman_goel_4bit.smt2").as_str())),
                ModelCheckResult::Success)
            )
        ;
    }

    #[ignore = "Need more PDR optimizations"]
    #[test]
    fn test_aman_goel() {
        dep_check();
        assert!(matches!(run_pdr_file("../inputs/unittest/aman_goel.btor", None), ModelCheckResult::Success));
    }
}
