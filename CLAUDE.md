# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Commands

```bash
# Build
cargo build
cargo build --release -p bmc   # specific tool

# Test
cargo test                          # all workspace tests
cargo test -p patronus              # core library only
cargo test -p patronus simplify     # tests matching "simplify" in core lib
cargo test -- --list                # list all tests

# Format check (required by CI)
cargo fmt --check
cargo fmt                           # auto-fix

# Python bindings (from python/)
uv sync --locked --all-extras --dev
uv run pytest
uv run pytest tests/test_mc.py     # single test file
```

## Architecture

Patronus is a hardware bug-finding toolkit that works on BTOR2 hardware description files. The core flow is: **BTOR2 → TransitionSystem → SMT encoding → solver → witness**.

### Workspace layout

- `patronus/` — core library; everything else depends on this
- `patronus-egraphs/` — e-graph integration using the `egg` crate
- `patronus-dse/` — dynamic symbolic execution (experimental)
- `tools/{bmc,sim,simplify,view,egraphs-cond-synth}/` — CLI frontends
- `python/` — PyO3 bindings published as `pypatronus`
- `inputs/` — test cases (BTOR2 files, SMT-LIB2 examples, repair benchmarks)

### Core library (`patronus/src/`)

The library is organized into five modules, each with a `mod.rs`-style re-export at the top level:

**`expr/`** — Expression IR (the central abstraction)
- `context.rs`: `Context` is an interning arena for all expressions and strings. Build expressions through `ctx.bv_*()` / `ctx.array_*()` methods; identical expressions get identical `ExprRef` handles (non-zero u32).
- `nodes.rs`: `Expr` enum — bit-vector ops (arith, bitwise, shifts, comparisons), array read/write, ITE, symbols, literals.
- `simplify.rs`: Constant folding and algebraic rewrites; returns a new `ExprRef` from the same context.
- `eval.rs`: Evaluates expressions given concrete variable assignments.
- `serialize.rs` / `parse.rs`: Round-trip text representation.
- `traversal.rs` / `transform.rs`: Bottom-up traversal and rewriting utilities.

**`system/`** — Transition systems
- `transition_system.rs`: `TransitionSystem` holds states (with `init` and `next` expressions), inputs, outputs, `bad_states` (safety properties), and `constraints`.
- `analyze.rs` / `transform.rs`: Analysis and transformation passes over a system.

**`btor2/`** — BTOR2 format
- `parse.rs`: Produces a `(Context, TransitionSystem)` pair from a BTOR2 file.
- `witness.rs`: Parses and prints counterexample witnesses.

**`smt/`** — SMT solver interface
- `solver.rs`: `SolverContext` trait — `assert`, `check_sat`, `push`/`pop`, `get_value`. Implementations communicate via stdin/stdout (SMT-LIB2 protocol) with bitwuzla, z3, cvc5, or yices2.
- `parser.rs` (43 KB): Full SMT-LIB2 response parser.
- `serialize.rs`: Encodes `ExprRef` nodes to SMT-LIB2 commands.

**`mc/`** — Model checking
- `bmc.rs`: Bounded Model Checking — unrolls the `TransitionSystem` for `k` steps, asserts each `bad_state` is reachable, queries the solver, and returns a `Witness` on SAT.
- `types.rs`: `ModelCheckResult`, `Witness`, `InitValue`.

**`sim/`** — Simulation
- `interpreter.rs`: Evaluates a `TransitionSystem` step by step with concrete values.
- `interface.rs`: Public API; `wave.rs` writes FST waveforms.

### Key design rules

- **All expressions are interned through `Context`.** Never construct `Expr` directly; use `ctx.bv_add(a, b)` etc. Two structurally equal expressions always compare equal as `ExprRef`.
- **`ExprRef` and `StringRef` are non-zero u32 handles** — cheap to copy and compare, zero-cost in `Option`.
- SMT logic is `QF_BV` or `QF_AUFBV` (with arrays). Solver is selected at call time; bitwuzla is the default in the BMC tool.
- Snapshot tests use the `insta` crate with YAML output (`cargo test` + `cargo insta review` to accept).

### CI

The CI matrix (`.github/workflows/test.yml`) runs: unit tests, BMC tool against Quiz1/2/4 benchmarks with all four solvers, simulator tool, e-graph synth, SMT simplify, Python bindings, `cargo fmt`, and `cargo-semver-checks`.
