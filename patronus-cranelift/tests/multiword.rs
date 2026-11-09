use baa::BitVecOps;
use patronus::btor2;
use patronus::expr::Context;
use patronus::sim::Simulator;

use patronus::sim::InitKind;

use patronus_cranelift::JITEngine;

const COUNT_2: &str = r#"
1 sort bitvec 65
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
fn jit_wide_literal() {
    let mut ctx = Context::default();
    let sys = btor2::parse_str(
        &mut ctx,
        r#"
        1 sort bitvec 65
        2 zero 1
        3 state 1
        4 init 1 3 2
        5 one 1

        "#,
        Some("count2"),
    )
    .unwrap();
    let counter_state = sys.states[0].symbol;
    let mut sim = JITEngine::new(&ctx, &sys);

    // init
    sim.init(InitKind::Zero);
    let baa::Value::BitVec(b) = sim.get(counter_state) else {
        panic!("did not get bitvec back")
    };
    assert!(b.is_zero());
    // println!("{:?}", sim.get(counter_state));
}

#[test]
fn jit_wide_slice() {
    let mut ctx = Context::default();
    let sys = btor2::parse_str(
        &mut ctx,
        r#"
        1 sort bitvec 65
        2 zero 1
        3 sort bitvec 4
        4 state 3
        5 one 1
        6 slice 3 5 3 0
        7 next 3 4 6
        "#,
        Some("count2"),
    )
    .unwrap();
    let counter_state = sys.states[0].symbol;
    let mut sim = JITEngine::new(&ctx, &sys);

    // init
    sim.init(InitKind::Zero);
    let baa::Value::BitVec(b) = sim.get(counter_state) else {
        panic!("did not get bitvec back")
    };
    assert!(b.is_zero());

    sim.step();
    let baa::Value::BitVec(b) = sim.get(counter_state) else {
        panic!("did not get bitvec back")
    };
    assert!(b.is_one());
}

#[test]
fn jit_wide_slice_span() {
    let mut ctx = Context::default();
    let sys = btor2::parse_str(
        &mut ctx,
        r#"
        1 sort bitvec 128
        2 consth 1 abcdabcdabcdabcdabcdabcdabcdabcd
        3 sort bitvec 10
        4 state 3
        6 slice 3 2 72 63
        7 next 3 4 6
        "#,
        Some("count2"),
    )
    .unwrap();
    let counter_state = sys.states[0].symbol;
    let mut sim = JITEngine::new(&ctx, &sys);

    // init
    sim.init(InitKind::Zero);
    let baa::Value::BitVec(b) = sim.get(counter_state) else {
        panic!("did not get bitvec back")
    };
    // assert!(b.is_zero());

    sim.step();
    let baa::Value::BitVec(b) = sim.get(counter_state) else {
        panic!("did not get bitvec back")
    };

    // TODO: this is wrong!
    // assert!(b.is_one());
    println!("{:?}", b);
}

#[test]
fn jit_wide_concat() {
    let mut ctx = Context::default();
    let sys = btor2::parse_str(
        &mut ctx,
        r#"
        1 sort bitvec 64
        2 zero 1
        3 sort bitvec 128
        4 state 3
        5 one 1
        6 concat 3 5 2
        7 next 3 4 6
        "#,
        Some("count2"),
    )
    .unwrap();
    let counter_state = sys.states[0].symbol;
    let mut sim = JITEngine::new(&ctx, &sys);

    // init
    sim.init(InitKind::Zero);
    let baa::Value::BitVec(b) = sim.get(counter_state) else {
        panic!("did not get bitvec back")
    };
    assert!(b.is_zero());

    sim.step();
    let baa::Value::BitVec(b) = sim.get(counter_state) else {
        panic!("did not get bitvec back")
    };
    assert_eq!(b.words()[0], 0);
    assert_eq!(b.words()[1], 1);
}
