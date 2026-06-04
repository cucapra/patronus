# PDR Implementation Review

Review of `patronus/src/mc/pdr.rs` against the FMCAD'11 PDR paper (Een/Mishchenko/Brayton)
and Pono's IC3Bits. No edits were made to the implementation.

**Updated 2026-06-04 (round 5).** Earlier rounds' resolved issues are collapsed into the
list below; only open issues carry full sections. Line numbers refer to the current file.

Test status: `test_trivial_fail` and `test_trivial_input_fail` pass.
**`test_simple_fail` hangs** — an infinite loop inside `block_cube` (Issue A below).

---

## Resolved (rounds 1-4, kept for traceability)

| Old # | Issue | Resolution |
|-------|-------|------------|
| 1 | Activation literals never declared | `declare_const` at `pdr.rs:352`, `pdr.rs:697` |
| 2 | `intersects_init` polarity inverted | asserts `cube.to_expr` (`pdr.rs:461`) |
| 3 | 0-step violation never checked | `init_check` (`pdr.rs:469-501`), called at `pdr.rs:912` |
| 6 | Clauses pushed into the infinite frame | push loop capped below `depth()` (`pdr.rs:730`) |
| 7 | INIT conjoined into the frontier query | `frame_assumptions` pure again; init assumption moved into `rel_ind_check` for frame 1 (`pdr.rs:528-530`) |
| 8 | Frame-0 Unsat arm fell through in `block_cube` | `continue` at `pdr.rs:810` |
| 9 | `rel_ind_check` panic on frame-0 cubes in the push loop | frame-0 branch routes to `intersects_init` (`pdr.rs:731-732`); residual decrement hazard absorbed into Issue A |
| 11 | `get_bad_cube` asserted unstepped bad expressions | fold over the stepped `bad_states` (`pdr.rs:423-426`) |

Old Issue 10 (push-loop evidence laundering) is also absorbed into Issue A — the round-4
edits turned the same root cause from a latent soundness hole into a live progress bug.

---

## Open issues

### A. Push-forward loop: blocked clauses land in invisible frames → infinite loop
**Status:** ❌ current `test_simple_fail` hang
**Locations:** probe `pdr.rs:738-741`, decrement `pdr.rs:748-749`, insertion `pdr.rs:758`;
interacts with `frame_assumptions` (`pdr.rs:384-402`) and `rel_ind_check`'s frame-1 init
assumption (`pdr.rs:528-530`)

#### Immediate bug
The loop now (correctly) probes `frame + 1`, but the `Sat` arm kept the old shape's
`gen_obj.frame -= 1`. Under probe-then-commit, `Sat` at `f+1` means *stay at `f`* — `f`
is already justified by the `solve_relative` UNSAT that led here. With the decrement,
every blocked cube is inserted one frame below its justification; obligations blocked at
**frame 1** land in `frames[0]`, which no query ever reads (`frame_assumptions(0)`
returns only the init literal; the assumption loop and propagation start at idx 1).

**`COUNT_2` trace at depth 3:**
1. Frontier finds `s@1=6, s@2=7` → obligation `(c₆, 2)`.
2. `rel_ind_check(c₆, 2)` SAT, predecessor `s=5` → push `(c₅, 1)`, re-push `(c₆, 2)`.
3. `(c₅, 1)` blocked (INIT-relative UNSAT) → generalize to `g₅` → probe
   `rel_ind_check(g₅, 2)` SAT (`s=4→5` unconstrained in `F_2`) → `frame = 0` →
   `¬g₅` inserted into `frames[0]` — invisible.
4. `(c₆, 2)` re-solved: `frame_assumptions(2)` can't see `frames[0]`, so `s=5` is found
   again → goto 3. Infinite loop (`cex_chain` also grows unboundedly).

#### Structural problem (why deleting the decrement is not enough)
For the parent obligation at frame `f+1` to stop re-deriving the same predecessor, the
learned clause must appear in the parent's assumption set, `frame_assumptions(f+1)` =
delta frames **≥ f+1**. Under the current `F_i` convention, a cube blocked at frame `f`
therefore needs insertion at `frames[f+1]`:

- For `f ≥ 2` that insertion is justified: the blocking UNSAT was relative to `F_f`, and
  predecessors of reach≤f+1 states lie in reach≤f ⊆ F_f.
- For `f == 1` it is **not**: the frame-1 check is INIT-relative (old Issue 7's fix), so
  its UNSAT only justifies `frames[1]` — but progress needs `frames[2]`. The hybrid
  convention has no single query that provides both. (This is old Issue 10's gap,
  resurfacing as a liveness bug.)

#### Recommended fix: full Een `F_{i-1}` convention
A small, coherent diff that dissolves the decrement hazard, the progress gap, and the
frame-0 special cases simultaneously:

1. `rel_ind_check`: use `frame_assumptions(proof_obj.frame - 1)`; delete the
   `frame == 1` init push (`frame_assumptions(0) = [init_assumption()]` supplies INIT
   automatically). Keep `assert_ne!(frame, 0)`.
2. Insertion at `frames[f]` becomes exactly justified **and** progress-making: the
   parent at `f+1` queries `frame_assumptions(f)`, which includes delta `f`.
3. Push loop — probe the next insertion point, never decrement:
   ```text
   k = blocked_cube.frame
   while k < depth-1 && rel_ind_check(cube, k+1) == Unsat:
       k += 1
   add_blocked_cube at frames[k]
   ```
   The frame-0 branch and the decrement (with its `assert!`) both disappear.
4. No other call sites change: `block_cube` already descends with `frame - 1`; frame-1
   SAT models are init states, so the frame-0 CEX case is unchanged; `propagate`'s check
   at `idx+1` becomes the textbook propagation query; `get_bad_cube` uses
   `frame_assumptions` directly and stays pure.

Sanity check on `COUNT_2`: `(c₅,1)` blocks relative to `F_0 = INIT` → `¬g₅` at
`frames[1]` → parent `(c₆,2)` queries `frame_assumptions(1)` ∋ `¬g₅` → `s=5` excluded →
`(c₆,2)` blocks at `frames[2]` → frontier stops finding `s=6` → depth advances.

### B. The counterexample chain is assembled incorrectly (old Issue 4)
**Status:** ❌ unchanged since round 1
**Locations:** `block_cube` `pdr.rs:797-805`, `pdr.rs:830-833`

- A `CexEntry` is pushed on every SAT `solve_relative` and never removed; backtracking
  and re-expanded parents leave stale/duplicate entries (the Issue A loop makes this
  visible as unbounded memory growth).
- Steps are mixed: descent entries read `NXT_STEP`, the init entry reads `CUR_STEP`;
  inputs don't line up with the transitions they drive.
- The chain never contains the actual bad state (`get_bad_cube` extracts the
  *predecessor*, `pdr.rs:436`), so `construct_witness` evaluates the bad expressions on
  a non-bad final entry → `failed_safety` comes out empty.

**Fix:** parent pointers per obligation; rebuild the path from the final frame-0
obligation; read inputs at the driving step; extend the trace one step to the bad state.

### C. `check_assuming_end` is never called (old Issue 5)
**Status:** ❌ unchanged since round 1
**Locations:** `check_assuming` sites `pdr.rs:434`, `pdr.rs:465`, `pdr.rs:493`, `pdr.rs:550`

No-op for bitwuzla; with yices2 (`supports_check_assuming = false`) every
`check_assuming` pushes and never pops, leaking assumptions into all later queries.
**Fix:** pair the calls, or require `check-sat-assuming` support.

---

## Minor / worth noting

- **`init_cube` uses the unstepped init expression** (`pdr.rs:344`). Fine for constant
  init values; init expressions referencing other signals reach the solver undeclared.
- **`get_bit_level_cube` arrays `todo!()`** (`pdr.rs:218`); `pdr.rs:902` panics on
  constrained systems. Both hard-crash rather than returning `Unknown`.
- **Solver-side clause leak:** subsumed cubes are removed from `self.cubes`
  (`pdr.rs:681`) but their `act ⇒ clause` assertions accumulate in the solver (inert).
- **`intersects_init` local still named `neg_cube_expr`** (`pdr.rs:461`); cosmetic.

---

## Suggested fix order

1. Issue A — the Een-convention switch (un-hangs `test_simple_fail`; also removes the
   frame-0/decrement special cases).
2. Issue B — witness correctness on non-trivial traces (next thing the now-reachable
   deep-CEX path will expose).
3. Issue C — portability to non-bitwuzla solvers.
