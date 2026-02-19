// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use patronus::expr::*;
use patronus::smt::{BITWUZLA, Solver};

#[derive(Default)]
struct Tester {
    simplifier: Simplifier<DenseExprMetaData<Option<ExprRef>>>,
    ctx: Context,
}

impl Drop for Tester {
    fn drop(&mut self) {
        // verify all rewrites with an SMT solver
        let mut solver = BITWUZLA
            .start(None)
            .expect("Failed to start bitwuzla. Is it installed?");
        self.simplifier
            .verify_simplification(&mut self.ctx, &mut solver)
            .expect("Failed to verify simplifications. Consult stdout!");
    }
}

impl Tester {
    /// test a simplification
    fn ts(&mut self, inp: &str, expect: &str) {
        let input = parse_expr(&mut self.ctx, inp);
        let expected = parse_expr(&mut self.ctx, expect);
        let simplified = self.simplifier.simplify(&mut self.ctx, input);
        assert_eq!(
            simplified,
            expected,
            "simplify({}) = {}\nExpected: {}",
            input.serialize_to_str(&self.ctx),
            simplified.serialize_to_str(&self.ctx),
            expected.serialize_to_str(&self.ctx)
        );
    }
}

#[test]
fn test_simplify_and() {
    let mut t = Tester::default();
    t.ts("true", "true");
    t.ts("false", "false");
    t.ts("and(true, false)", "false");
    t.ts("and(true, true)", "true");
    t.ts("and(a : bv<1>, true)", "a : bv<1>");
    t.ts("and(a : bv<3>, 3'b111)", "a : bv<3>");
    t.ts("and(a : bv<1>, false)", "false");
    t.ts("and(a : bv<3>, 3'b000)", "3'b000");
    t.ts("and(a : bv<1>, not(a))", "false");
    t.ts("and(not(a : bv<1>), a)", "false");

    // de morgan
    t.ts(
        "and(not(a:bv<3>), not(b:bv<3>))",
        "not(or(a:bv<3>, b:bv<3>))",
    );

    // and encoded xor (as one would get from an and-inverter-graph
    t.ts(
        "and(not(and(not(a:bv<3>), b:bv<3>)), not(and(not(b), a)))",
        "not(xor(a:bv<3>, b:bv<3>))",
    );
    t.ts(
        "not(and(not(and(not(a:bv<3>), b:bv<3>)), not(and(not(b), a))))",
        "xor(a:bv<3>, b:bv<3>)",
    );
    t.ts(
        "not(and(not(and(b:bv<3>, not(a:bv<3>))), not(and(not(b), a))))",
        "xor(b:bv<3>, a:bv<3>)",
    );
}

#[test]
fn test_simplify_or() {
    let mut t = Tester::default();
    t.ts("or(false, true)", "true");
    t.ts("or(false, false)", "false");
    t.ts("or(a : bv<1>, true)", "true");
    t.ts("or(a : bv<3>, 3'b111)", "3'b111");
    t.ts("or(a : bv<1>, false)", "a : bv<1>");
    t.ts("or(a : bv<3>, 3'b000)", "a : bv<3>");
    t.ts("or(a : bv<1>, not(a))", "true");
    t.ts("or(not(a : bv<1>), a)", "true");

    // de morgan
    t.ts(
        "or(not(a:bv<3>), not(b:bv<3>))",
        "not(and(a:bv<3>, b:bv<3>))",
    );

    // xor truth table (sum of products)
    t.ts(
        "or(and(not(a:bv<3>), b:bv<3>), and(not(b), a))",
        "xor(a:bv<3>, b:bv<3>)",
    );
}

#[test]
fn test_simplify_xor() {
    let mut t = Tester::default();
    t.ts("xor(false, true)", "true");
    t.ts("xor(false, false)", "false");
    t.ts("xor(true, true)", "false");
    t.ts("xor(a : bv<1>, a)", "false");
    t.ts("xor(a : bv<1>, not(a))", "true");
    t.ts("xor(not(a : bv<1>), a)", "true");
}

#[test]
fn test_simplify_not() {
    let mut t = Tester::default();
    t.ts("not(false)", "true");
    t.ts("not(true)", "false");
    t.ts("not(a: bv<1>)", "not(a: bv<1>)");
    t.ts("not(not(a: bv<1>))", "a: bv<1>");
    t.ts("not(not(not(a: bv<1>)))", "not(a: bv<1>)");
    t.ts("not(not(not(not(a: bv<1>))))", "a: bv<1>");
}

#[test]
fn test_simplify_zero_extend() {
    let mut t = Tester::default();
    t.ts("zext(false, 1)", "2'b00");
    t.ts("zext(true, 1)", "2'b01");
    t.ts("zext(true, 0)", "true");
    // zero extends always get normalized to a concat with zero
    t.ts("zext(a: bv<2>, 4)", "concat(4'd0, a: bv<2>)");
    t.ts("zext(zext(a: bv<2>, 4), 3)", "concat(7'd0, a: bv<2>)");
}

#[test]
fn test_simplify_sign_extend() {
    let mut t = Tester::default();
    t.ts("sext(false, 1)", "2'b00");
    t.ts("sext(true, 1)", "2'b11");
    t.ts("sext(true, 0)", "true");
    // combine sign extensions
    t.ts("sext(sext(a: bv<2>, 4), 3)", "sext(a : bv<2>, 7)");
}

#[test]
fn test_simplify_ite() {
    let mut t = Tester::default();
    // outcome is always the same
    t.ts("ite(c : bv<1>, a: bv<10>, a)", "a : bv<10>");

    // constant condition
    t.ts("ite(true, a: bv<10>, b: bv<10>)", "a : bv<10>");
    t.ts("ite(false, a: bv<10>, b: bv<10>)", "b : bv<10>");

    // both true and false value are boolean constants
    t.ts("ite(c : bv<1>, true, false)", "c : bv<1>");
    t.ts("ite(c : bv<1>, true, true)", "true");
    t.ts("ite(c : bv<1>, false, true)", "not(c : bv<1>)");
    t.ts("ite(c : bv<1>, false, false)", "false");

    // one value is a boolean constant
    t.ts("ite(c:bv<1>, true, b:bv<1>)", "or(c:bv<1>, b:bv<1>)");
    t.ts("ite(c:bv<1>, false, b:bv<1>)", "and(not(c:bv<1>), b:bv<1>)");
    t.ts("ite(c:bv<1>, a:bv<1>, false)", "and(c:bv<1>, a:bv<1>)");
    t.ts("ite(c:bv<1>, a:bv<1>, true)", "or(not(c:bv<1>), a:bv<1>)");
}

#[test]
fn test_simplify_slice() {
    let mut t = Tester::default();
    // slice a constant
    t.ts("3'b110[2]", "true");
    t.ts("3'b110[1]", "true");
    t.ts("3'b110[0]", "false");
    t.ts("4'b1100[3:2]", "2'b11");
    t.ts("4'b1100[2:1]", "2'b10");
    t.ts("4'b1100[1:0]", "2'b00");

    // nested slices
    t.ts("a : bv<10>[6:3][1]", "a : bv<10>[4]");
}

#[test]
fn test_simplify_shift_left() {
    let mut t = Tester::default();
    // shift a constant by a constant
    t.ts("shift_left(3'b011, 3'd0)", "3'b011");
    t.ts("shift_left(3'b011, 3'd1)", "3'b110");
    t.ts("shift_left(3'b011, 3'd2)", "3'b100");
    t.ts("shift_left(3'b011, 3'd3)", "3'b000");

    // shift by a constant
    t.ts("shift_left(a : bv<3>, 3'd0)", "a : bv<3>");
    t.ts(
        "shift_left(a : bv<3>, 3'd1)",
        "concat(a : bv<3>[1:0], 1'b0)",
    );
    t.ts("shift_left(a : bv<3>, 3'd2)", "concat(a : bv<3>[0], 2'b00)");
    t.ts("shift_left(a : bv<3>, 3'd3)", "3'b000");

    // more shift by constant tests
    t.ts("shift_left(a:bv<32>, 32'd0)", "a : bv<32>");
    t.ts(
        "shift_left(a:bv<32>, 32'd4)",
        "concat(a:bv<32>[27:0], 4'd0)",
    );
}

#[test]
fn test_simplify_shift_right() {
    let mut t = Tester::default();
    // shift a constant by a constant
    t.ts("shift_right(3'b101, 3'd0)", "3'b101");
    t.ts("shift_right(3'b101, 3'd1)", "3'b010");
    t.ts("shift_right(3'b101, 3'd2)", "3'b001");
    t.ts("shift_right(3'b101, 3'd3)", "3'b000");

    // shift by a constant
    t.ts("shift_right(a : bv<3>, 3'd0)", "a : bv<3>");
    t.ts(
        "shift_right(a : bv<3>, 3'd1)",
        "concat(1'd0, a : bv<3>[2:1])",
    );
    t.ts("shift_right(a : bv<3>, 3'd2)", "concat(2'd0, a : bv<3>[2])");
    t.ts("shift_right(a : bv<3>, 3'd3)", "3'b000");

    // more shift by constant tests
    t.ts("shift_right(a:bv<32>, 32'd0)", "a : bv<32>");
    t.ts(
        "shift_right(a:bv<32>, 32'd4)",
        "concat(4'd0, a:bv<32>[31:4])",
    );
}

#[test]
fn test_simplify_arithmetic_shift_right() {
    let mut t = Tester::default();
    // shift a constant by a constant
    t.ts("arithmetic_shift_right(3'b101, 3'd0)", "3'b101");
    t.ts("arithmetic_shift_right(3'b101, 3'd1)", "3'b110");
    t.ts("arithmetic_shift_right(3'b101, 3'd2)", "3'b111");
    t.ts("arithmetic_shift_right(3'b101, 3'd3)", "3'b111");

    // shift by a constant
    t.ts("arithmetic_shift_right(a : bv<3>, 3'd0)", "a : bv<3>");
    t.ts(
        "arithmetic_shift_right(a : bv<3>, 3'd1)",
        "sext(a : bv<3>[2:1], 1)",
    );
    t.ts(
        "arithmetic_shift_right(a : bv<3>, 3'd2)",
        "sext(a : bv<3>[2], 2)",
    );
    t.ts(
        "arithmetic_shift_right(a : bv<3>, 3'd3)",
        "sext(a : bv<3>[2], 2)",
    );
}

#[test]
fn test_simplify_add() {
    let mut t = Tester::default();
    // add constants
    t.ts("add(true, true)", "false");
    t.ts("add(true, false)", "true");
    t.ts("add(false, false)", "false");
    t.ts("add(15'd123, 15'd321)", "15'd444");

    // add zero
    t.ts("add(a : bv<4>, 4'd0)", "a : bv<4>");
    t.ts("add(4'd0, a : bv<4>)", "a : bv<4>");
}

#[test]
fn test_simplify_mul() {
    let mut t = Tester::default();
    // multiply constants
    t.ts("mul(true, true)", "true");
    t.ts("mul(true, false)", "false");
    t.ts("mul(false, false)", "false");
    t.ts("mul(17'd123, 17'd321)", "17'd39483");

    // multiply with zero
    t.ts("mul(a : bv<4>, 4'd0)", "4'd0");
    t.ts("mul(4'd0, a : bv<4>)", "4'd0");

    // multiply with one
    t.ts("mul(a : bv<4>, 4'd1)", "a : bv<4>");
    t.ts("mul(4'd1, a : bv<4>)", "a : bv<4>");

    // multiply with power of two (this includes a simplification of the left shift)
    t.ts("mul(a : bv<4>, 4'd2)", "concat(a : bv<4>[2:0],  1'b0)");
    t.ts("mul(a : bv<4>, 4'd4)", "concat(a : bv<4>[1:0], 2'b00)");
    t.ts("mul(a : bv<4>, 4'd8)", "concat(a : bv<4>[0],  3'b000)");
}

#[test]
fn test_simplify_concat() {
    let mut t = Tester::default();
    // normalize concats
    t.ts(
        "concat(concat(a : bv<1>, b:bv<1>), c:bv<1>)",
        "concat(a : bv<1>, concat(b:bv<1>, c:bv<1>))",
    );

    // concat constants
    t.ts("concat(3'b110, 2'b01)", "5'b11001");
    t.ts("concat(3'b110, concat(false, true))", "5'b11001");
    t.ts("concat(concat(3'b110, false), true)", "5'b11001");

    // concat constants in the presence of other expressions
    t.ts(
        "concat(a : bv<3>, concat(false, true))",
        "concat(a:bv<3>, 2'b01)",
    );
    t.ts(
        "concat(concat(a : bv<3>, false), true)",
        "concat(a:bv<3>, 2'b01)",
    );
    t.ts(
        "concat(true, concat(false, a : bv<3>))",
        "concat(2'b10, a:bv<3>)",
    );
    t.ts(
        "concat(concat(true, false), a : bv<3>)",
        "concat(2'b10, a:bv<3>)",
    );
    t.ts(
        "concat(3'b101, concat(true, concat(false, a : bv<3>)))",
        "concat(5'b10110, a:bv<3>)",
    );
}

#[test]
fn test_simplify_implies() {
    let mut t = Tester::default();
    t.ts("implies(false, a : bv<1>)", "true");
    t.ts("implies(false, true)", "true");
    t.ts("implies(false, false)", "true");
    t.ts("implies(true, a : bv<1>)", "a : bv<1>");
    t.ts("implies(true, true)", "true");
    t.ts("implies(true, false)", "false");
}

#[test]
fn test_simplify_ugte() {
    let mut t = Tester::default();
    t.ts("ugte(1'b0, 1'b1)", "false");
    t.ts("ugte(1'b1, 1'b0)", "true");
    t.ts("ugte(1'b1, 1'b1)", "true");
    t.ts("ugte(1'b0, 1'b0)", "true");
    t.ts("ugte(3'b101, 3'b011)", "true");
    t.ts("ugte(3'b011, 3'b101)", "false");
    t.ts("ugte(4'd7, 4'd7)", "true");
    t.ts("ugte(4'd15, 4'd10)", "true");
    t.ts("ugte(4'd5, 4'd10)", "false");
}

// from maltese-smt:
// https://github.com/ucb-bar/maltese-smt/blob/main/test/maltese/smt/SMTSimplifierSpec.scala
#[test]
fn test_simplify_bool_equality() {
    let mut t = Tester::default();
    t.ts("eq(b : bv<1>, true)", "b : bv<1>");
    t.ts("eq(b : bv<1>, false)", "not(b : bv<1>)");
    t.ts("eq(false, b : bv<1>)", "not(b : bv<1>)");
}

// from maltese-smt
#[test]
fn test_simplify_comparison_to_concat() {
    let mut t = Tester::default();
    // eq over concat should be split up
    t.ts(
        "eq(c:bv<5>, concat(a:bv<2>, b:bv<3>))",
        "and(eq(a:bv<2>, c:bv<5>[4:3]), eq(b:bv<3>,c[2:0]))",
    );
    t.ts(
        "eq(concat(a:bv<2>, b:bv<3>), c:bv<5>)",
        "and(eq(a:bv<2>, c:bv<5>[4:3]), eq(b:bv<3>,c[2:0]))",
    );

    // now with nested concats
    t.ts(
        "eq(c:bv<5>, concat(concat(a1:bv<1>, a0:bv<1>), b: bv<3>))",
        "and(eq(a1:bv<1>, c:bv<5>[4]), and(eq(a0:bv<1>, c[3]), eq(b:bv<3>, c[2:0])))",
    );
}

#[test]
fn test_simplify_comparison_to_zero_extend() {
    let mut t = Tester::default();
    // all of this is solved by a combination of simplifying:
    //  - comparison to concat
    //  - pushing slice into concat
    //  - normalizing zero extend as concat with zeros
    t.ts("eq(4'd0, zext(a:bv<5>, 4)[8:5])", "true");
    t.ts("eq(4'd1, zext(a:bv<5>, 4)[8:5])", "false");
    t.ts("eq(2'b10, zext(a:bv<1>, 1))", "false");
    t.ts("eq(concat(4'd0, a:bv<5>), zext(a:bv<5>, 4))", "true");
}

// from maltese-smt
#[test]
fn test_simplify_bit_masks() {
    let mut t = Tester::default();
    t.ts(
        "and(concat(a: bv<2>, b: bv<3>), 5'b11000)",
        "concat(a:bv<2>, 3'd0)",
    );
    t.ts(
        "and(concat(a: bv<2>, b: bv<3>), 5'b10000)",
        "concat(a:bv<2>[1], 4'd0)",
    );
    t.ts(
        "and(concat(a: bv<2>, b: bv<3>), 5'b01000)",
        "concat(1'd0, concat(a:bv<2>[0], 3'd0))",
    );
    t.ts(
        "and(concat(a: bv<2>, b: bv<3>), 5'b00100)",
        "concat(2'd0, concat(b:bv<3>[2], 2'd0))",
    );
    t.ts(
        "and(concat(a: bv<2>, b: bv<3>), 5'b00010)",
        "concat(3'd0, concat(b:bv<3>[1], 1'd0))",
    );
    t.ts(
        "and(concat(a: bv<2>, b: bv<3>), 5'b00001)",
        "concat(4'd0, b:bv<3>[0])",
    );
}

// from maltese-smt
#[test]
fn test_simplify_slice_on_sign_extension() {
    let mut t = Tester::default();
    // sext is essentially like a concat, and thus we want to push the slice into it
    t.ts("sext(a:bv<4>, 2)[3:0]", "a:bv<4>");
    t.ts("sext(a:bv<4>, 2)[3:1]", "a:bv<4>[3:1]");
    t.ts("sext(a:bv<4>, 2)[2:1]", "a:bv<4>[2:1]");
    t.ts("sext(a:bv<4>, 2)[4:0]", "sext(a:bv<4>, 1)");
    t.ts("sext(a:bv<4>, 2)[5:0]", "sext(a:bv<4>, 2)");
    t.ts("sext(a:bv<4>, 2)[4:1]", "sext(a:bv<4>[3:1], 1)");
}

#[test]
fn test_push_slice_into_concat() {
    let mut t = Tester::default();
    // slice on a concat should become part of that concat
    t.ts(
        "concat(a:bv<3>, b:bv<2>)[3:0]",
        "concat(a:bv<3>[1:0], b:bv<2>)",
    );
    t.ts(
        "concat(a:bv<3>, b:bv<2>)[3:1]",
        "concat(a:bv<3>[1:0], b:bv<2>[1])",
    );
    t.ts("concat(a:bv<3>, b:bv<2>)[3:2]", "a:bv<3>[1:0]");
    t.ts("concat(a:bv<3>, b:bv<2>)[1:0]", "b:bv<2>");
    t.ts("concat(a:bv<3>, b:bv<2>)[1]", "b:bv<2>[1]");

    // non-overlapping slice of 2-concat
    t.ts("concat(3'b011, a : bv<2>)[4:2]", "3'b011");
    t.ts("concat(3'b011, a : bv<2>)[4:3]", "2'b01");
    t.ts("concat(3'b011, a : bv<2>)[1:0]", "a : bv<2>");
    t.ts("concat(3'b011, a : bv<2>)[1]", "a : bv<2>[1]");

    // overlapping slice of 2-concat
    t.ts("concat(3'b011, a : bv<2>)[4:0]", "concat(3'b011, a:bv<2>)");
    t.ts(
        "concat(3'b011, a : bv<2>)[4:1]",
        "concat(3'b011, a:bv<2>[1])",
    );
    t.ts("concat(3'b011, a : bv<2>)[3:0]", "concat(2'b11, a:bv<2>)");

    // non-overlapping slice of 3-concat
    t.ts("concat(concat(a:bv<2>, 3'b011), b : bv<2>)[6:5]", "a:bv<2>");
    t.ts("concat(a:bv<2>, concat(3'b011, b : bv<2>))[6:5]", "a:bv<2>");
    t.ts("concat(concat(a:bv<2>, 3'b011), b : bv<2>)[4:2]", "3'b011");
    t.ts("concat(a:bv<2>, concat(3'b011, b : bv<2>))[4:2]", "3'b011");
    t.ts("concat(concat(a:bv<2>, 3'b011), b : bv<2>)[1:0]", "b:bv<2>");
    t.ts("concat(a:bv<2>, concat(3'b011, b : bv<2>))[1:0]", "b:bv<2>");

    // overlapping slice of 3-concat
    t.ts(
        "concat(concat(a:bv<2>, 3'b011), b : bv<2>)[6:2]",
        "concat(a:bv<2>, 3'b011)",
    );
    t.ts(
        "concat(a:bv<2>, concat(3'b011, b : bv<2>))[6:2]",
        "concat(a:bv<2>, 3'b011)",
    );
    t.ts(
        "concat(concat(a:bv<2>, 3'b011), b : bv<2>)[6:3]",
        "concat(a:bv<2>, 2'b01)",
    );
    t.ts(
        "concat(a:bv<2>, concat(3'b011, b : bv<2>))[6:3]",
        "concat(a:bv<2>, 2'b01)",
    );
    t.ts(
        "concat(concat(a:bv<2>, 3'b011), b : bv<2>)[5:2]",
        "concat(a:bv<2>[0], 3'b011)",
    );
    t.ts(
        "concat(a:bv<2>, concat(3'b011, b : bv<2>))[5:2]",
        "concat(a:bv<2>[0], 3'b011)",
    );
}

#[test]
fn test_slice_of_ite() {
    let mut t = Tester::default();
    t.ts(
        "ite(c:bv<1>, a:bv<4>, b:bv<4>)[0]",
        "ite(c:bv<1>, a:bv<4>[0], b:bv<4>[0])",
    );
}

#[test]
fn test_simplify_concat_of_adjacent_slices() {
    let mut t = Tester::default();
    t.ts("concat(a:bv<32>[20:19], a[18:0])", "a:bv<32>[20:0]");
    t.ts("concat(a:bv<32>[31:19], a[18:0])", "a:bv<32>");
}

#[test]
fn test_simplify_slice_of_op() {
    let mut t = Tester::default();
    // push into not
    t.ts("not(a:bv<32>)[20:1]", "not(a:bv<32>[20:1])");
    t.ts("not(a:bv<32>)[15:0]", "not(a:bv<32>[15:0])");

    // push slice into neg, which we can only for msbs
    t.ts("neg(a:bv<32>)[20:1]", "neg(a:bv<32>)[20:1]");
    t.ts("neg(a:bv<32>)[15:0]", "neg(a:bv<32>[15:0])");

    // push into bit-wise and arithmetic binary ops
    for op in ["and", "or", "xor", "add", "sub", "mul"] {
        t.ts(
            &format!("{op}(a:bv<32>, b:bv<32>)[30:0]"),
            &format!("{op}(a:bv<32>[30:0], b:bv<32>[30:0])"),
        );
        if op == "and" || op == "or" || op == "xor" {
            t.ts(
                &format!("{op}(a:bv<32>, b:bv<32>)[30:2]"),
                &format!("{op}(a:bv<32>[30:2], b:bv<32>[30:2])"),
            );
        } else {
            t.ts(
                &format!("{op}(a:bv<32>, b:bv<32>)[30:2]"),
                &format!("{op}(a:bv<32>, b:bv<32>)[30:2]"),
            );
        }

        // examples that show up in actual code
        t.ts(
            &format!("{op}(zext(a:bv<32>, 1), zext(b:bv<32>, 1))[31:0]"),
            &format!("{op}(a:bv<32>, b:bv<32>)"),
        );
    }
}

#[test]
fn test_random_z3_issue_simplification() {
    let mut t = Tester::default();
    // someone was trying to simplify this with z3: https://github.com/Z3Prover/z3/issues/7460
    // z3 currently returns:
    // Concat(Extract(14, 0, V), 0) | Concat(0, Extract(15, 0, V)) >> 15
    // -> or(concat(V[14:0], 0), shift_right(concat(0, V[15:0]), 15))
    // it is nice to see that z3 implements some bit-mask support similar to ours
    // we currently do slightly better by simplifying away the right shift by a constant
    t.ts(
        "or(shift_left(and(V : bv<32>, 32'd65535), 32'd17), shift_right(and(V, 32'd65535), 32'd15))",
        "or(concat(V:bv<32>[14:0], 17'x00000), concat(31'x00000000, V[15]))",
    );
}

#[test]
fn test_bool_from_gate_level() {
    let mut t = Tester::default();
    // this formula is from a gate-level adder circuit
    t.ts(
        "and(not(and(not(c:bv<1>), not(b:bv<1>))), not(and(c, b)))",
        "xor(c:bv<1>, b:bv<1>)",
    );
}

// TODO: add missing literals simplifications: https://github.com/ekiwi/maltese-private/blob/main/test/maltese/smt/SMTSimplifierLiteralsSpec.scala
