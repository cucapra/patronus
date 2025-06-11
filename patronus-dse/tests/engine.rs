// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use patronus::expr::{Context, ExprRef};
use patronus::sim::InitKind;
use patronus::*;
use patronus_dse::{SymEngine, ValueSummary};

const COUNT_2: &str = r#"
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
"#;

/// This test is a "symbolic" version of the `interpret_count_2` test.
/// The execution is actually 100% concrete because the system lacks an input and we initialize
/// all state to a concrete value.
#[test]
fn test_exec_count_2() {
    let mut ctx = Context::default();
    let sys = btor2::parse_str(&mut ctx, COUNT_2, Some("count2")).unwrap();
    let counter_state = sys.states[0].symbol;
    let bad = sys.bad_states[0];
    let mut sim = SymEngine::new(&ctx, sys);

    fn v(v: ValueSummary<ExprRef>) -> u64 {
        v.concrete()
            .expect("not concrete!")
            .try_into_u64()
            .expect("cannot be represented by a u64")
    }

    // init
    sim.init(&mut ctx, InitKind::Zero);
    assert_eq!(v(sim.get(counter_state)), 1);
}
