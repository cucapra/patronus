# Copyright 2025 Cornell University
# Copyright 2025 The Regents of the University of California
# released under BSD 3-Clause License
# author: Kevin Laeufer <laeufer@cornell.edu>
# author: Adwait Godbole <adwait@berkeley.edu>

import pathlib
import pytest
from patronus import *


repo_root = (pathlib.Path(__file__) / '..' / '..' / '..').resolve()

COUNT_2 = """
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
"""

def test_parse_and_serialize_count2():
    sys = parse_btor2_str(COUNT_2, "count2")
    assert sys.name == "count2"

    expected_system = """
count2
bad _bad_0 : bv<1> = eq(_state_0, 3'b111)
state _state_0 : bv<3>
  [init] 3'b000
  [next] add(_state_0, 3'b001)
    """
    assert expected_system.strip() == str(sys).strip()

def test_transition_system_fields():
    sys = parse_btor2_str(COUNT_2, "count2")
    assert sys.inputs == []
    assert sys.constraints == []
    assert [str(e) for e in sys.bad_states] == ["eq(_state_0, 3'b111)"]
    assert len(sys.states) == 1
    state = sys.states[0]
    assert state.name == "_state_0"
    assert str(state.symbol) == "_state_0"
    assert str(state.init) == "3'b000"
    assert str(state.next) == "add(_state_0, 3'b001)"
    assert len(sys.outputs) == 0


def test_expression_builder():
    # we are emulating the Z3 API as much as possible
    a = BitVec('a', 3)
    b = BitVec('b', 3)
    assert str(a < b) == "sgt(b, a)"


def test_transition_system_builder():
    sys = TransitionSystem("test")
    en, count_s = BitVec('en', 1), BitVec('count_s', 8)
    sys.inputs = [en]
    sys.states = [State('count_s', init=BitVecVal(0, 8), next=If(en, count_s + BitVecVal(1, 8), count_s))]
    sys.outputs = [Output('count', count_s)]
    # TODO: there is a big pitfall here: you cannot just `append` to the bad_states, inputs, etc. because we use
    #       a getter / setter approach
    sys.bad_states = [count_s == BitVecVal(123, 8)]
    expected_system = """
test
input en : bv<1>
output count : bv<8> = count_s
bad %18 : bv<1> = eq(count, 8'b01111011)
state count_s : bv<8>
  [init] 8'b00000000
  [next] ite(en, add(count, 8'b00000001), count)
    """
    assert str(sys).strip() == expected_system.strip()


