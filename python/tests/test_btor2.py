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
    filename = repo_root / "inputs" / "chiseltest" / "Quiz1.btor"
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
