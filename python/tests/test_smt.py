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

