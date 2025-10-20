# Copyright 2025 Cornell University
# released under BSD 3-Clause License
# author: Kevin Laeufer <laeufer@cornell.edu>

import pathlib
import pytest
from patronus import *

repo_root = (pathlib.Path(__file__) / '..' / '..' / '..').resolve()



def test_transition_system_simulation():
    sys = parse_btor2_file(repo_root / "inputs" / "unittest" / "swap.btor")
    sim = Interpreter(sys)
    a, b = sys['a'].symbol, sys['b'].symbol

    sim.init()
    assert sim[a] == 0, "a@0"
    assert sim[b] == 1, "b@0"

    sim.step()
    assert sim[a] == 1
    assert sim[b] == 0

    sim.step()
    assert sim[a] == 0
    assert sim[b] == 1
