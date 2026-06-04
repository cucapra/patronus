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
fn test_dep_check() {
    INIT.call_once(|| {
        assert!(bitwuzla_exists());
    });
}

// SMT output directory
const SMT_OUT: &str = "patronus/tests/smt_out";

// Trivial circuit whose initial state violates the safety property
const TRIVIAL_FAIL: &str =  r"
1 sort bitvec 1
2 ones 1
3 state 1
4 init 1 3 2
5 next 1 3 2
6 bad 3
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
            let file = std::fs::File::create(out_file).unwrap();
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
        test_dep_check();
        // run_pdr_str(TRIVIAL_FAIL, Some(format!("{SMT_OUT}/trivial_fail.smt2").as_str()));
        assert!(matches!(run_pdr_str(TRIVIAL_FAIL, None), ModelCheckResult::Fail(_)));
    }
}
