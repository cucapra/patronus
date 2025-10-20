# Copyright 2025 Cornell University
# released under BSD 3-Clause License
# author: Kevin Laeufer <laeufer@cornell.edu>

from patronus import *

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


