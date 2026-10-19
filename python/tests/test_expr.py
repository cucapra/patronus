# Copyright 2025 Cornell University
# released under BSD 3-Clause License
# author: Kevin Laeufer <laeufer@cornell.edu>

from pypatronus import *


def test_simplify():
    # by default this uses a global simplifier
    true = BitVecVal(1, 1)
    false = BitVecVal(0, 1)
    a = BitVec("a", 1)
    assert simplify((~a) & a) == false
    assert simplify((~a) | a) == true

    assert simplify(SignExt(1, false)) == BitVecVal(0b00, 2)
    assert simplify(SignExt(1, true)) == BitVecVal(0b11, 2)

    assert (
        simplify(BitVecVal(0, 4).equals(Extract(8, 5, ZeroExt(4, BitVec("a", 5)))))
        == true
    )


def test_expr_sort():
    bv_1 = BitVecVal(1, 1).sort()
    assert bv_1 == BitVecSort(1)
    assert BitVecVal(1, 1).sort() == BoolSort(), (
        "in patronus bv<1> and bool are the same"
    )


def test_expr_introspection():
    a = BitVec("a", 1)
    assert a.op() == Op.BVSymbol
    assert a.width() == 1
    a_and_b = a & BitVec("b", 1)
    assert a_and_b.op() == Op.BVAnd
    assert a_and_b.width() == 1
    assert str(a_and_b.op()) == "Op.BVAnd"
    assert a_and_b.op().snake_case() == "bv_and"
    arg_a, arg_b = a_and_b.args()
    assert arg_a == a
    assert arg_b.name() == "b"


def test_expressions_hash():
    a = BitVec("a", 1)
    d = {a: 1}
    d[a] += 1
    assert d[a] == 2
    a_and_b = a & BitVec("b", 1)
    d[a_and_b] = 2
    d[a_and_b] += 2
    assert d[a_and_b] == 4
    assert id(a) != id(a_and_b)
    d[BitVec("a", 1) & BitVec("b", 1)] += 1
    assert d[a_and_b] == 5


def test_find_symbols():
    a = BitVec("a", 1)
    b = BitVec("b", 1)
    a_and_b = a & b
    assert a_and_b.symbols() == {a, b}
    assert a.symbols() == {a}
    assert b.symbols() == {b}


def test_expr_replacement():
    a = BitVec("a", 1)
    b = BitVec("b", 1)
    x = BitVec("x", 1)
    a_and_b = a & b
    x_and_b = a_and_b.replace({a: x})
    a_and_x = a_and_b.replace({b: x})
    b_and_a = a_and_b.replace({b: a, a: b})
    assert x_and_b == x & b
    assert a_and_x == a & x
    assert b_and_a == b & a
