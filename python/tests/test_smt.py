# Copyright 2025 Cornell University
# released under BSD 3-Clause License
# author: Kevin Laeufer <laeufer@cornell.edu>

import pathlib
import pytest
from patronus import *

repo_root = (pathlib.Path(__file__) / '..' / '..' / '..').resolve()

def test_call_smt_solver():
    a = BitVec('a', 3)
    b = BitVec('b', 3)
    s = Solver('z3')
    r = s.check(a < b)
    assert str(r) == "sat"

    r = s.check(a < b, a > b)
    assert str(r) == "unsat"

    # to generate a model, we need to actually add the assertion!
    s.add(a < b)
    s.check()
    m = s.model()
    assert len(m) == 2
    assert isinstance(m[a], int)
    assert isinstance(m[b], int)
    assert m[a] < m[b]


def test_parse_smt_lib_expr():
    symbols = {
        'x_0': BitVec('x_0', 32),
        'y_0': BitVec('y_0', 32),
        'x_1': BitVec('x_1', 32),
    }
    a = parse_smtlib_expr("(= x_1 (bvadd x_0 y_0))", symbols)
    assert str(a) == "eq(x_1, add(x_0, y_0))"


@pytest.mark.skip(reason="parsing commands is not implemented yet")
def test_parse_smt_lib_commands():
    parse_smtlib_cmd("(set-logic QF_BV)")
    parse_smtlib_cmd("(set-option :produce-models true)")
    parse_smtlib_cmd("(declare-const x_0 (_ BitVec 32))")
