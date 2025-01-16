// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use patronus::btor2;
use patronus::expr::Context;
use patronus::sim::Simulator;
use patronus::sim::{InitKind, Interpreter};

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

#[test]
fn interpret_count_2() {
    let mut ctx = Context::default();
    let sys = btor2::parse_str(&mut ctx, COUNT_2, Some("count2")).unwrap();
    let counter_state = sys.states[0].symbol;
    let bad = sys.bad_states[0];
    let mut sim = Interpreter::new(&ctx, &sys);

    // init
    sim.init(InitKind::Zero);
    sim.update();
    assert_eq!(sim.get(counter_state).try_into_u64().unwrap(), 0);

    // increment counter by one
    sim.step();
    sim.update();
    assert_eq!(sim.get(counter_state).try_into_u64().unwrap(), 1);

    // save state
    let at_one = sim.take_snapshot();

    // increment counter to three
    sim.step();
    sim.update();
    sim.step();
    sim.update();
    assert_eq!(sim.get(counter_state).try_into_u64().unwrap(), 3);

    // save state again
    let at_three = sim.take_snapshot();

    // restore state
    sim.restore_snapshot(at_one);
    sim.update();
    assert_eq!(sim.get(counter_state).try_into_u64().unwrap(), 1);
    sim.step();
    sim.update();
    assert_eq!(sim.get(counter_state).try_into_u64().unwrap(), 2);

    // restore again
    sim.restore_snapshot(at_three);
    sim.update();
    assert_eq!(sim.get(counter_state).try_into_u64().unwrap(), 3);

    // make bad condition fail
    while sim.get(bad).try_into_u64().unwrap() == 0 {
        sim.step();
        sim.update();
    }

    // the failure is reached when the state is 7
    assert_eq!(sim.get(counter_state).try_into_u64().unwrap(), 7);
}

#[test]
fn interpret_delay() {
    let (ctx, sys) = btor2::parse_file("../inputs/unittest/delay.btor").unwrap();
    let reg0 = sys.get_state_by_name(&ctx, "reg0").unwrap().symbol;
    let reg1 = sys.get_state_by_name(&ctx, "reg1").unwrap().symbol;
    let mut sim = Interpreter::new(&ctx, &sys);

    // init
    sim.init(InitKind::Zero);
    sim.update();
    assert_eq!(sim.get(reg0).try_into_u64().unwrap(), 0, "reg0@0");
    assert_eq!(sim.get(reg1).try_into_u64().unwrap(), 0, "reg1@0");

    // step 1
    sim.step();
    sim.update();
    assert_eq!(sim.get(reg0).try_into_u64().unwrap(), 1, "reg0@1");
    assert_eq!(sim.get(reg1).try_into_u64().unwrap(), 0, "reg1@1");

    // step 2
    sim.step();
    sim.update();
    assert_eq!(sim.get(reg0).try_into_u64().unwrap(), 1, "reg0@2");
    assert_eq!(sim.get(reg1).try_into_u64().unwrap(), 1, "reg1@2");
}

#[test]
fn interpret_swap() {
    let (ctx, sys) = btor2::parse_file("../inputs/unittest/swap.btor").unwrap();
    let a = sys.get_state_by_name(&ctx, "a").unwrap().symbol;
    let b = sys.get_state_by_name(&ctx, "b").unwrap().symbol;
    let mut sim = Interpreter::new(&ctx, &sys);

    // init
    sim.init(InitKind::Zero);
    sim.update();
    assert_eq!(sim.get(a).try_into_u64().unwrap(), 0, "a@0");
    assert_eq!(sim.get(b).try_into_u64().unwrap(), 1, "b@0");

    // step 1
    sim.step();
    sim.update();
    assert_eq!(sim.get(a).try_into_u64().unwrap(), 1, "a@1");
    assert_eq!(sim.get(b).try_into_u64().unwrap(), 0, "b@1");

    // step 2
    sim.step();
    sim.update();
    assert_eq!(sim.get(a).try_into_u64().unwrap(), 0, "a@2");
    assert_eq!(sim.get(b).try_into_u64().unwrap(), 1, "b@2");
}
