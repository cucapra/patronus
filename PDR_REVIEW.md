# PDR Implementation Review

Review of `patronus/src/mc/pdr.rs` against the FMCAD'11 PDR paper (Een/Mishchenko/Brayton)
and Pono's IC3Bits. No edits were made to the implementation.

Test status: `cargo test -p patronus --test pdr` currently **fails** at the first solver
assertion with `undefined symbol 'act_0'` (Issue 1).

---

## Critical — nothing runs yet

### 1. Activation literals are never declared to the solver
**Locations:** `pdr.rs:331`, `pdr.rs:595` (asserted at `pdr.rs:346`, `pdr.rs:605-607`)

```rust
let init_act = ctx.bv_symbol("act_0", 1);   // :331 — creates a Context node only
...
smt_ctx.assert(ctx, imp)?;                  // :346 — references act_0, never declared
```

`ctx.bv_symbol(...)` only interns a symbol in the `Context`; it does not emit a
`(declare-const act_0 ...)` to the solver. Every other symbol in this codebase reaches the
solver through `smt_ctx.declare_const(...)` (e.g. `bmc.rs:476`, `bmc.rs:513`). `declare_const`
is **never** called anywhere in `pdr.rs`.

**Fix:** call `smt_ctx.declare_const(ctx, init_act)?` in `init()` and
`smt_ctx.declare_const(ctx, act)?` in `add_blocked_cube()` before the symbols are used in
assertions/assumptions.

---

## Soundness — can report wrong results once it runs

### 2. INIT is not enforced in the relative-induction / generalization checks
**Locations:** `rel_ind_check` `pdr.rs:438`, `generalize` `pdr.rs:515`, `frame_assumptions` `pdr.rs:375`

`frame_assumptions(i)` iterates `i..=depth()`, so for any `frame >= 1` it **excludes frame 0**
(the init cube). Thus `rel_ind_check` for `frame > 0` asserts only `F_i ∧ ¬c ∧ T ∧ c'` and
never constrains the cube against INIT.

The PDR/IC3 invariant requires a blocked cube to satisfy **both** `INIT ⇒ ¬c` and
`F_i ∧ ¬c ∧ T ⇒ ¬c'`. The first half is only checked for the *original* bad cube, when the
obligation descends to `frame == 0` (`pdr.rs:640`). But `generalize` (`pdr.rs:528-556`) drops
literals and re-validates **only via `rel_ind_check` at `frame > 0`**, with no INIT constraint.
So generalization can drop a literal until the cube intersects an initial state, then block its
negation.

**Concrete failure:** `INIT = {s == 1}` (width 2), bad cube `{s0==1, s1==1}` (s==3). Generalize
drops `s1==1` → `{s0==1}` (s odd, which *includes* s==1). The `frame>0` check can return UNSAT,
the clause `(s0==0)` is added to `F_i`, and now `F_i` excludes the initial state. Propagation
can then declare an "inductive invariant" that doesn't contain a reachable state → **false
`Success` on an unsafe system.**

**Fix:** also assert `INIT ∧ c_reduced` is UNSAT before accepting a dropped literal (or include
the init frame in the assumption set for the generalization queries), mirroring Pono's init label.

### 3. The 0-step (initial-state) property violation is never checked
**Location:** `get_bad_cube` `pdr.rs:399-404`

`get_bad_cube` only ever evaluates the bad states at `NXT_STEP`:
```rust
sys.bad_states.iter().map(|b| enc.get_at(ctx, *b, NXT_STEP))
```
and `start_bmc_or_pdr` doesn't check bad states at step 0 either. So the algorithm only finds
states that *transition into* a bad state. A system whose **initial state itself violates P but
has no bad successor** is reported `Success`. The trivial test only passes because there
`next == ones`, so the init state also has a bad successor.

**Fix:** add an explicit `INIT ∧ ¬P` check up front (cf. Pono's `check_init`).

---

## Witness generation

### 4. The counterexample chain is assembled incorrectly
**Locations:** `block_cube` `pdr.rs:643-652`, `pdr.rs:662-676`

`block_cube` is a priority-queue (min-by-frame) search, but the CEX is built as if it were a
single linear descent:

- A `CexEntry` is pushed on **every** SAT `solve_relative` (`pdr.rs:673`) and never removed.
  When a descent branch hits `frame 0` UNSAT (`pdr.rs:654 continue`) and the search backtracks to
  a re-pushed `proof_obj` (`pdr.rs:670`), the entries from the dead branch remain in `cex_chain`.
  The chain returned at `pdr.rs:652` therefore contains states not on the real path.
- The step at which values are read is mixed: descent entries read `NXT_STEP` states+inputs
  (`pdr.rs:674-675`) while the init entry reads `CUR_STEP` (`pdr.rs:646-647`). The input driving a
  transition is the *current*-step input, so inputs won't line up with transitions even on a clean
  path.

For the single-step trivial case this happens to produce a valid witness, but any non-trivial
trace with backtracking will be wrong.

**Fix:** record a parent pointer per proof obligation and reconstruct the path from the final
frame-0 obligation, rather than appending to a shared `Vec`.

---

## Correctness on non-default solvers

### 5. `check_assuming_end` is never called
**Locations:** all `check_assuming` call sites — `pdr.rs:418`, `pdr.rs:482`

In `bmc.rs`, every `check_assuming` is paired with `check_assuming_end` (which does a `pop` for
solvers where `supports_check_assuming == false`). `pdr.rs` calls `check_assuming` many times and
never calls `check_assuming_end`. For bitwuzla (`supports_check_assuming = true`) this is a no-op,
so the test path is unaffected — but with **yices2** (`supports_check_assuming = false`,
`solver.rs:409`) `check_assuming` does `push; assert...; check_sat` and never pops, so assumptions
leak across queries and corrupt every subsequent result.

**Fix:** pair the calls, or require `check-sat-assuming` support (the activation-literal design
really wants it anyway).

---

## Minor / worth noting

- **Frame-index convention differs from Pono.** Obligation `(c, i)` is blocked using
  `frame_assumptions(i) = F_i` (`pdr.rs:446`) and the clause is added at `F_i`
  (`pdr.rs:700`/`pdr.rs:598`). Pono and the paper check relative to **F_{i-1}**. Using `F_i` (the
  weaker frame) is still *sound* — a strictly harder query — but it generalizes less and deviates
  from the reference; confirm it's intentional.
- **`init_cube` uses the unstepped init expression** (`pdr.rs:338`): `ctx.equal(sym, init)` with
  `init = state.init`. Fine for constant init values, but if an init expression references other
  signals it should be lifted with `expr_at_step`/`enc.get_at` at `CUR_STEP`.
- **`get_bit_level_cube` arrays `todo!()`** (`pdr.rs:214`) will panic on any system with array
  state; `pdr.rs:767` `assert!(sys.constraints.is_empty())` panics on constrained systems. Both
  hard-crash rather than returning `Unknown`.
- **Subsumed cubes leak** (`pdr.rs:579-592`): cubes removed from frame lists stay in `self.cubes`,
  and their `act ⇒ clause` assertion stays in the solver (inert, since the act literal is no longer
  assumed). Memory-only, not a correctness issue.

---

## Suggested fix order

1. Issue 1 (declaration) — required for the algorithm to execute at all.
2. Issues 2 and 3 — can make PDR return an outright wrong answer.
3. Issue 4 — witness correctness on non-trivial traces.
4. Issue 5 — portability to non-bitwuzla solvers.
