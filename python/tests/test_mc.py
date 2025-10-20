# Copyright 2025 Cornell University
# released under BSD 3-Clause License
# author: Kevin Laeufer <laeufer@cornell.edu>

import pathlib
import pytest
from patronpy import *

repo_root = (pathlib.Path(__file__) / '..' / '..' / '..').resolve()



def test_transition_system_model_checking():
    sys = parse_btor2_file(repo_root / "inputs" / "unittest" / "swap.btor")
    mc = SmtModelChecker('z3')
    # there are no assertions in this circuit, so it cannot fail
    assert str(mc.check(sys, 4)) == "unsat"

    # add an assertion
    a = next(s.symbol for s in sys.states if str(s.symbol) == 'a')
    b = next(s.symbol for s in sys.states if str(s.symbol) == 'b')
    sys.add_assertion("a_is_0", a.equals(BitVecVal(0, 8)))
    r = mc.check(sys, 4)
    assert str(r) == "sat"

    # check model
    assert len(r) == 2, "fail in step 2"

    # check initial values
    # TODO!
    # assert r[a] == BitVecVal(0, 8)
    # assert r[b] == BitVecVal(1, 8)