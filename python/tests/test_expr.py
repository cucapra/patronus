# Copyright 2025 Cornell University
# released under BSD 3-Clause License
# author: Kevin Laeufer <laeufer@cornell.edu>

from pypatronus import *

def test_simplify():
    # by default this uses a global simplifier
    true = BitVecVal(1, 1)
    false = BitVecVal(0,1)
    a = BitVec('a', 1)
    assert simplify((~a) & a) == false
    assert simplify((~a) | a) == true

    assert simplify(SignExt(1, false)) == BitVecVal(0b00, 2)
    assert simplify(SignExt(1, true)) == BitVecVal(0b11, 2)

    assert simplify(BitVecVal(0, 4).equals(Extract(8, 5, ZeroExt(4, BitVec('a', 5))))) == true


def test_expr_introspection():
    a = BitVec('a', 1)
    assert a.op() == Op.BVSymbol
    assert a.width() == 1
    a_and_b = a & BitVec('b', 1)
    assert a_and_b.op() == Op.BVAnd
    assert a_and_b.width() == 1
    assert str(a_and_b.op()) == 'Op.BVAnd'
    arg_a, arg_b = a_and_b.args()
    assert arg_a == a
    assert arg_b.name() == "b"