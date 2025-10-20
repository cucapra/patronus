# Copyright 2025 Cornell University
# released under BSD 3-Clause License
# author: Kevin Laeufer <laeufer@cornell.edu>

import pathlib
import pytest
from patronus import *

repo_root = (pathlib.Path(__file__) / '..' / '..' / '..').resolve()



def test_transition_system_model_checking():
    sys = parse_btor2_file(repo_root / "inputs" / "unittest" / "swap.btor")
    mc = SmtModelChecker('z3')
    mc.check(sys, 4)