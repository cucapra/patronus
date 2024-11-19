// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use patronus::expr::*;

/// test a simplification
fn ts(inp: &str, expect: &str) {
    let mut ctx = Context::default();
    let input = parse_expr(&mut ctx, inp);
    let expected = parse_expr(&mut ctx, expect);
    let simplified = simplify_single_expression(&mut ctx, input);
    assert_eq!(
        simplified,
        expected,
        "simplify({}) = {}\nExpected: {}",
        input.serialize_to_str(&ctx),
        simplified.serialize_to_str(&ctx),
        expected.serialize_to_str(&ctx)
    );
}

#[test]
fn test_simplify_and() {
    ts("true", "true");
    ts("false", "false");
    ts("and(true, false)", "false");
    ts("and(true, true)", "true");
    ts("and(a : bv<1>, true)", "a : bv<1>");
    ts("and(a : bv<3>, 3'b111)", "a : bv<3>");
    ts("and(a : bv<1>, false)", "false");
    ts("and(a : bv<3>, 3'b000)", "3'b000");
    ts("and(a : bv<1>, not(a))", "false");
    ts("and(not(a : bv<1>), a)", "false");
}

#[test]
fn test_simplify_or() {
    ts("or(false, true)", "true");
    ts("or(false, false)", "false");
    ts("or(a : bv<1>, true)", "true");
    ts("or(a : bv<3>, 3'b111)", "3'b111");
    ts("or(a : bv<1>, false)", "a : bv<1>");
    ts("or(a : bv<3>, 3'b000)", "a : bv<3>");
    ts("or(a : bv<1>, not(a))", "true");
    ts("or(not(a : bv<1>), a)", "true");
}

#[test]
fn test_simplify_xor() {
    ts("xor(false, true)", "true");
    ts("xor(false, false)", "false");
    ts("xor(true, true)", "false");
    ts("xor(a : bv<1>, a)", "false");
    ts("xor(a : bv<1>, not(a))", "true");
    ts("xor(not(a : bv<1>), a)", "true");
}

#[test]
fn test_simplify_not() {
    ts("not(false)", "true");
    ts("not(true)", "false");
    ts("not(a: bv<1>)", "not(a: bv<1>)");
    ts("not(not(a: bv<1>))", "a: bv<1>");
    ts("not(not(not(a: bv<1>)))", "not(a: bv<1>)");
    ts("not(not(not(not(a: bv<1>))))", "a: bv<1>");
}

#[test]
fn test_simplify_zext() {
    ts("zext(false, 1)", "2'b00");
    ts("zext(true, 1)", "2'b01");
    ts("zext(true, 0)", "true");
}

#[test]
fn test_simplify_sext() {
    ts("sext(false, 1)", "2'b00");
    ts("sext(true, 1)", "2'b11");
    ts("sext(true, 0)", "true");
}

#[test]
fn test_simplify_ite() {
    // outcome is always the same
    ts("ite(c : bv<1>, a: bv<10>, a)", "a : bv<10>");

    // constant condition
    ts("ite(true, a: bv<10>, b: bv<10>)", "a : bv<10>");
    ts("ite(false, a: bv<10>, b: bv<10>)", "b : bv<10>");

    // both true and false value are boolean constants
    ts("ite(c : bv<1>, true, false)", "c : bv<1>");
    ts("ite(c : bv<1>, true, true)", "true");
    ts("ite(c : bv<1>, false, true)", "not(c : bv<1>)");
    ts("ite(c : bv<1>, false, false)", "false");
}

#[test]
fn test_simplify_slice() {
    // slice a constant
    ts("3'b110[2]", "true");
    ts("3'b110[1]", "true");
    ts("3'b110[0]", "false");
    ts("4'b1100[3:2]", "2'b11");
    ts("4'b1100[2:1]", "2'b10");
    ts("4'b1100[1:0]", "2'b00");

    // nested slices
    ts("a : bv<10>[6:3][1]", "a : bv<10>[4]");
}

#[test]
fn test_simplify_shift_left() {}