# Issue A in Detail: Invisible Blocked Clauses and the Frame-Index Accounting Mismatch

Companion to `PDR_REVIEW.md` (round 5, Issue A). Explains the `test_simple_fail` infinite
loop in `patronus/src/mc/pdr.rs` from first principles. There are three layers: a
mechanical bug, a visibility rule, and a deeper accounting mismatch.

**Round-6 update:** a fix was attempted (decrement removed; INIT dropped from the
frame-1 query). It resolves Layer 1 only — the test still hangs, and the INIT removal
reopens a soundness hole. See "Round-6 attempt" at the bottom for the analysis and the
remaining one-line fix.

---

## Layer 0: what `frames[j]` actually means

`frames` is a **delta encoding**. `frames[j]` does *not* store "the clauses of F_j" — it
stores clauses tagged with their **expiry index**:

> a clause `¬c` stored at `frames[j]` means: "every state reachable in ≤ j steps
> satisfies `¬c`."

The frame *predicate* F_i used in queries is assembled from all clauses whose expiry is
≥ i:

```
F_i  =  clauses in frames[i] ∪ frames[i+1] ∪ ... ∪ frames[depth]
        (this is exactly what frame_assumptions(i) activates, pdr.rs:392)
```

Two consequences drive everything else:

1. Storing a clause at a **higher** index is a **stronger claim** (it joins more
   frames), so it requires more proof.
2. A query at frame `i` can only "see" clauses stored at index ≥ i. Clauses below `i`
   are invisible to it.

---

## Layer 1: the mechanical bug (the decrement)

The pre-round-4 loop shape was *check-at-f, then increment*: it re-ran the check at the
current frame, and on a `Sat` at some later frame `g` it stepped back to `g-1` — always
≥ the entry frame, so the decrement was a legitimate "undo the last optimistic
increment."

The round-4 loop probes `frame + 1` (`pdr.rs:738-741`, the correct probe-then-commit
shape) but kept the decrement (`pdr.rs:748-749`). On the very first iteration: enter at
frame `f` (already proven blocked there by `solve_relative`), probe `f+1`, get `Sat`.
The right conclusion is "can't advance — stay at `f`." The decrement instead concludes
`f-1` — *below* the frame that was already proven.

For an obligation blocked at frame 1, that's `frames[0]`, and by consequence #2 above
index 0 is read by **no query at all**: `frame_assumptions(0)` returns only the init
literal (`pdr.rs:385-387`), the clause loop starts at `frame_idx ≥ 1`, and propagation
starts at idx 1. The clause is learned into a black hole.

---

## Layer 2: why that produces an infinite loop, not just slowness

Consider what the **parent** obligation does after its child is blocked. The parent
`(p, f+1)` ran the query

```
SAT?[ frame_assumptions(f+1)  ∧  ¬p  ∧  T  ∧  p' ]
```

got `Sat`, and the CUR-state model *was* the child cube `c`. The parent is re-pushed
and, once the child is dealt with, runs **the exact same query again**. The only thing
that changed in the solver in between is some new `act ⇒ clause` implications — but the
query only *activates* literals from `frames[f+1..]`. So:

> If `¬c` was stored anywhere below index `f+1`, the parent's re-query is logically
> identical to the first one — and the solver is free (and in practice likely) to hand
> back the **same model** `c` again.

Same model → same child obligation → child blocks again → clause stored in the same
invisible place → parent re-queries → same model. That is the cycle. Concretely on
`COUNT_2` (3-bit counter, bad at 7) at depth 3:

```
(c₆, 2):  F₂ ∧ ¬c₆ ∧ T ∧ c₆'  →  SAT, predecessor s=5     ──┐
(c₅, 1):  INIT-relative check  →  UNSAT, blocked             │
          generalize → g₅; probe at 2 → Sat → frame 1-1 = 0  │
          ¬g₅ stored in frames[0]    ← invisible to ALL queries
(c₆, 2):  re-query reads frames[2..] only → s=5 again      ──┘  forever
```

The loop is not "PDR being slow" — the worklist literally cycles through identical
states because the learning never lands where the re-query looks. (This is also why
`cex_chain` grows without bound: an entry is pushed on every parent re-expansion —
see Issue B.)

---

## Layer 3: the accounting mismatch (why deleting the decrement isn't enough)

Issue A can now be stated as a mismatch between two ledgers:

- **What's proven** (soundness ledger): how high may I store `¬c`?
- **What's needed** (progress ledger): how high must I store `¬c` so the parent
  sees it?

The progress ledger is fixed by Layer 2: the parent at `f+1` reads index ≥ `f+1`, so
storage at **`frames[f+1]`** is needed.

The soundness ledger depends on which query produced the UNSAT:

- **Pure check at frame `f ≥ 2`** (`F_f ∧ ¬c ∧ T ∧ c'` UNSAT): justifies
  `frames[f+1]`. Induction: a state reached in ≤ f+1 steps has a predecessor reached in
  ≤ f steps; that predecessor lies in F_f and satisfies `¬c`; the UNSAT says no such
  predecessor enters `c`. Proven = f+1 = needed. ✓
- **Frame-1 check** — INIT-relative since the round-3 fix (`pdr.rs:528-530`): the UNSAT
  only says "no *initial* state steps into `c`." That covers reachability in ≤ 1 step →
  justifies `frames[1]` only. The parent at frame 2 needs `frames[2]`.
  Proven = 1 < needed = 2. ✗

That is the hole: at frame 1, *no amount of fixing the loop arithmetic helps*, because
the hybrid convention never executes the query (pure `F₁ ∧ ¬c ∧ T ∧ c'`) whose UNSAT
would license index 2. The hole was created when INIT moved into the frame-1 check — it
fixed the earlier false-`Success` and dead-end problems but quietly broke the
proven/needed alignment at exactly one frame.

---

## Why the Een `F_{i-1}` convention closes it

Een's choice — query obligation `(c, i)` relative to **F_{i-1}**, with F_0 = INIT — is
not an indexing taste. It is the unique alignment where the two ledgers agree *at every
frame*:

| | hybrid (current) | Een `F_{i-1}` |
|---|---|---|
| block `(c,f)` query relative to | F_f (INIT∧F₁ if f=1) | F_{f-1} (INIT if f=1) |
| UNSAT justifies storing at | f+1 (but only 1 if f=1) | **f** |
| parent `(p, f+1)` reads | index ≥ f+1 | index ≥ **f** |
| proven vs. needed | mismatched at f=1 | **equal, all f** |

Under Een, the parent's query is itself relative to F_f = `frames[f..]`, so a clause
stored at index `f` — exactly what the child's UNSAT proves — is *guaranteed* visible to
the parent's re-query. The model that produced the child is excluded; the parent must
either find a genuinely different predecessor or go UNSAT. Progress is structural, not
incidental. The frame-1 special case dissolves too: `frame_assumptions(0) = [act_0]`
already *is* the F_0 = INIT assumption set, so `rel_ind_check(frame=1)` picks up INIT
with no injected special case.

This is also why the push loop becomes trivial under Een — start at the proven index
`f`, probe whether `k+1`'s query (relative to F_k) is UNSAT, and step up while it is:

```text
k = blocked_cube.frame
while k < depth-1 && rel_ind_check(cube, k+1) == Unsat:
    k += 1
add_blocked_cube at frames[k]
```

Every committed index is backed by exactly its own query; there is nothing to
decrement, ever. The frame-0 branch and the `assert!(frame > 0)` disappear with it.

Sanity check on `COUNT_2` under the Een scheme: `(c₅,1)` blocks relative to
`F_0 = INIT` → `¬g₅` at `frames[1]` → parent `(c₆,2)` queries `frame_assumptions(1)` ∋
`¬g₅` → `s=5` excluded → `(c₆,2)` blocks at `frames[2]` → frontier stops finding `s=6` →
depth advances. Termination restored.

---

## Round-6 attempt: decrement removed, INIT dropped from frame 1 — still hangs

The attempted fix made three edits:

1. The push loop's `Sat` arm now just `break`s — the decrement is gone (`pdr.rs:742-746`). ✓
2. `add_blocked_cube` asserts `blocked_cube.frame > 0` (`pdr.rs:696`) — frame-0
   pollution now fails loudly. ✓
3. The `frame == 1` init push was **deleted from `rel_ind_check`** — the query is back
   to the pure `F_i` convention at every frame. ✗ (wrong half of the change)

Verified empirically: the test suite still hangs (`timeout 20` kill).

### Why it still hangs: Layer 1 fixed, Layers 2-3 untouched

`rel_ind_check` still uses `frame_assumptions(proof_obj.frame)` (`pdr.rs:522`). Closing
the `frames[0]` black hole just moves the cycle up one index: the clause now lands at
`frames[1]`, which is *equally invisible* to a parent at frame 2. `COUNT_2` at depth 3:

```
(c₆, 2):  SAT, predecessor s=5 → push (c₅, 1)                          ──┐
(c₅, 1):  blocked (F₁ ∋ s<4 from depth 2) → generalize → g₅ = {5,7}     │
          probe at frame 2 → Sat (s=4→5 unconstrained in F₂) → break    │
          ¬g₅ inserted at frames[1]   ← invisible to frame_assumptions(2)
(c₆, 2):  re-query reads delta[2..] only → s=5 again                  ──┘  forever
```

This is exactly the Layer-3 prediction ("deleting the decrement is not enough"): when
the probe at `f+1` fails, insertion stops at `f`, and under the `F_i` convention the
parent at `f+1` never reads index `f`. The proven/needed ledgers are still misaligned —
now at every frame, not just frame 1.

### New regression: the initiation-only 0→1 advance is unsound

Dropping INIT from the frame-1 query reverted half of the round-4 Issue 7 fix instead of
moving the convention down by one. Consequences:

1. **Frame-0 obligations with non-init cubes are reachable again** — frame-1 SAT models
   are no longer init states, so descents hit `block_cube`'s frame-0 `Unsat` arm (e.g.
   `(c₅, 0)` arises on `COUNT_2` at depth 2).
2. **The push loop advances 0 → 1 on initiation evidence alone.** From frame 0 it
   probes `intersects_init` (`pdr.rs:728-729`) and on Unsat inserts at `frames[1]`.
   That membership claims "reach≤1 ⇒ ¬c", but no query ever checked that an init state
   cannot *step into* `c` (consecution). Counterexample shape: `init s=0`, `T: 0→4`;
   cube `{s=4}` passes initiation (4 ∉ INIT), so `¬{s≥4}` is inserted at `frames[1]` —
   wrongly excluding the 1-step-reachable state 4 → masked frontier → potential false
   `Success`. It is harmless on `COUNT_2` only by luck of the transition function.

### The remaining fix is one line (plus one branch deletion)

The round-6 push loop is already the correct probe-then-commit shape for the Een
convention — probe `frame+1`, increment on Unsat, never decrement. What's left:

1. **`pdr.rs:522`**: `frame_assumptions(proof_obj.frame)` →
   `frame_assumptions(proof_obj.frame - 1)`. `frame_assumptions(0)` already returns
   `[init_assumption()]`, so frame-1 queries pick up INIT automatically — restoring
   frame-1 soundness *and* making frame-0 obligations dead code again.
2. **Delete the frame-0 branch in the push loop** (`pdr.rs:728-729`): probe
   `rel_ind_check` at `gen_obj.frame + 1` unconditionally. `frame+1 ≥ 1` always
   satisfies the assert, and from frame 0 the probe becomes relative to
   `frame_assumptions(0)` = INIT — the *consecution* check that the `intersects_init`
   probe was wrongly standing in for.

After that the ledgers align (see the table above): blocked-at-`f` is proven relative to
`F_{f-1}`, stored at `frames[f]`, and read by the parent's query relative to `F_f`. On
`COUNT_2`: `¬g₅` at `frames[1]` kills `s=5` in `(c₆,2)`'s re-query → `(c₆,2)` blocks at
`frames[2]` → frontier stops finding 6 → depth advances → terminates with `Fail`.

**Post-fix expectation:** the `Fail` verdict will be correct, but the witness will be
wrong — Issue B (`PDR_REVIEW.md`): `cex_chain` accumulates duplicated/misaligned entries
from parent re-expansions, mixes `CUR_STEP`/`NXT_STEP` reads, and never contains the
actual bad state.

---

## One-sentence summary

A blocked cube must be stored at an index the parent's re-query actually reads; under
the `F_i` convention the proven index always falls one short of that (round 5: the
decrement pushed it lower still, into invisible `frames[0]`; round 6: it lands at
`frames[f]`, still invisible to the parent at `f+1`) — switching every query to
`F_{i-1}` makes "what you proved" and "what the parent reads" the same index by
construction, and as of round 6 that switch is a one-line change.
