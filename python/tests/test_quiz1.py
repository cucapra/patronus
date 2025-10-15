import pathlib
import pytest

from patronus import parse


repo_root = (pathlib.Path(__file__) / '..' / '..' / '..').resolve()


def test_parse_and_index_quiz1():
    btor_path = repo_root / "inputs" / "chiseltest" / "Quiz1.btor"
    assert btor_path.is_file(), f"missing BTOR test input at {btor_path}"

    design = parse(str(btor_path))
    n = len(design)
    assert n > 0

    # Index access for a handful of nodes should return a dict with at least a 'kind'
    sample_count = min(n, 50)
    saw_symbol = False
    saw_literal = False
    saw_op_with_children = False

    for i in range(sample_count):
        node = design[i]
        assert isinstance(node, dict), f"node {i} is not a dict"
        assert "kind" in node, f"node {i} missing 'kind'"
        k = node["kind"]

        if k == "BVSymbol" or k == "ArraySymbol":
            assert "name" in node and isinstance(node["name"], str)
            saw_symbol = True

        if k == "BVLiteral":
            assert "width" in node and "value" in node
            saw_literal = True

        # Check a few common ops have integer child refs
        if k in {"BVAdd", "BVAnd", "BVOr", "BVEqual", "BVNot", "BVIte", "BVSlice"}:
            # Determine expected child fields
            if k in {"BVAdd", "BVAnd", "BVOr", "BVEqual"}:
                assert isinstance(node["a"], int) and isinstance(node["b"], int)
                saw_op_with_children = True
            elif k == "BVNot":
                assert isinstance(node["e"], int)
                saw_op_with_children = True
            elif k == "BVIte":
                assert isinstance(node["cond"], int)
                assert isinstance(node["tru"], int)
                assert isinstance(node["fals"], int)
                saw_op_with_children = True
            elif k == "BVSlice":
                assert isinstance(node["e"], int)
                assert isinstance(node["hi"], int)
                assert isinstance(node["lo"], int)
                saw_op_with_children = True

    assert saw_symbol, "did not encounter any symbol nodes in the first batch"
    assert saw_literal, "did not encounter any literal nodes in the first batch"
    assert saw_op_with_children, "did not encounter any ops with children in the first batch"


def test_out_of_range_index_raises():
    # Use a tiny BTOR file to parse, then index out of bounds
    btor_path = repo_root / "inputs" / "chiseltest" / "Quiz1.btor"
    design = parse(str(btor_path))
    with pytest.raises(IndexError):
        _ = design[len(design)]
