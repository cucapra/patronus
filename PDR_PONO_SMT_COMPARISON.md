# SMT Query Comparison: patronus PDR vs. Pono IC3Bits

Comparison of the SMT-LIB sessions produced by `patronus/src/mc/pdr.rs` and Pono's
`ic3bits` engine on the six PDR test inputs. Dumps live in
`patronus/tests/patronus_out/` and `patronus/tests/pono_out/` (same file names).

## Methodology

- **patronus**: each test passes `BITWUZLA.start(Some(file))`, capturing the literal
  bitwuzla stdin session (`tests/pdr.rs`).
- **Pono**: `docker run --init --rm -v <dir>:/work pono -e ic3bits -k 1000
  --printing-smt-solver <file>.btor`, capturing stderr (smt-switch's printing-solver
  wrapper; backend is also bitwuzla/bzla). `-k 1000` is required — Pono's default
  `-k 10` bound truncates IC3 and returns `unknown` on `aman_goel_4bit`.
- Both dumps are "commands issued to the solver", not solver-internal effort; they are
  directly comparable at the protocol level.
- The Pono copies of the inputs needed sanitizing for btor2tools (strip `;` comments,
  squeeze double spaces, renumber `swap.btor`'s out-of-order `next` id) — patronus'
  parser is more lenient.
- `delay.btor` and `swap.btor` contain **no `bad` property**: Pono refuses to run them,
  and patronus returns `Success` from the empty-`bad_states` early-exit before issuing
  any query. Their `pono_out` files are explanatory placeholders, and the corresponding
  patronus tests currently exercise only the parser, not PDR.

## Headline numbers

Verdicts agree on all four runnable tests (sat=Fail ×3, unsat=Success ×1).

| metric (aman_goel_4bit unless noted) | patronus | Pono ic3bits |
|---|---|---|
| total sat-checks: trivial_fail | 1 | 1 |
| total sat-checks: trivial_input_fail | 3 | 2 |
| total sat-checks: simple_fail | **126** | **63** |
| total sat-checks: aman_goel_4bit | **1251** (867 two-step, 384 cur-step) | **1001** (354 `check-sat`, 647 `check-sat-assuming`) |
| `get-unsat-assumptions` | **0** | **206** |
| `push`/`pop` pairs | 0 | 1001 (one scope per query) |
| `get-value` calls | 117 (word-level) | 484 (bit-level) |
| clause additions | 49 asserts (avg 3.7 literals) | 500 frame-label asserts (avg 2.8 bit-literals, incl. per-frame duplicates) |
| frames at convergence | n/a (not visible in dump) | 14 (simple_fail: 5) |
| solver resets | 0 | 11 (`reset-assertions`) |

## Architectural differences

### 1. Encoding: 2-step unrolling vs. labeled single-step pair

patronus unrolls two steps up front: `u@1`, `u@2` declared, with the transition
relation baked in permanently as `define-fun`/`define-const` bindings of the `@2`
symbols. Every query — including current-step-only ones like `intersects_init` —
carries the transition definitions (harmless but always present).

Pono declares one current/next pair (`state5`, `state5.pono_generated__next`) and puts
the transition relation behind an activation literal:

```
(assert (=> __trans_label (and true (= state3.pono_generated__next (bvadd state3 #b001)))))
```

so T participates only in queries that assert `__trans_label`. Initiation and
generalization-initiation queries are genuinely T-free.

### 2. Frame representation: per-clause activation vs. per-frame label

- **patronus**: one activation literal **per clause** (`act_N ⇒ clause`), delta
  encoding, frames activated by listing every live clause's literal in
  `check-sat-assuming`. Measured on aman_goel_4bit: **avg 10.9 / median 8 / max 43
  activation literals per query**, growing with the live clause count. Each clause is
  asserted exactly once (49 asserts total); retired/subsumed clauses stay in the solver
  as inert gated assertions forever (no reset mechanism).
- **Pono**: one label **per frame** (`__frame_label_i`); adding a clause to frame `i`
  is `(assert (=> __frame_label_i clause))`, and a query activates a frame with a
  single `(assert __frame_label_i)` inside a `push`/`pop` scope. Query preambles stay
  O(1) regardless of clause count, at the cost of **re-asserting clauses on
  propagation** (500 label-asserts on aman_goel_4bit vs. patronus' 49; 30 vs. 13 on
  simple_fail) and re-asserting the cube per scope (~11.7 asserts/query). Pono also
  periodically rebuilds the solver (`reset-assertions` ×11) to clear accumulated
  garbage — patronus has no analogue (the known inert-assertion leak).

Net: patronus is leaner on asserts; Pono is leaner on per-query assumption lists and
has a garbage-collection story. At these sizes neither dominates; at thousands of
clauses, patronus' linearly growing assumption lists and unbounded gated garbage will
hurt first.

### 3. The big functional gap: unsat-core generalization

This is the most consequential difference, and it is visible directly in the dumps:

- Pono issues `check-sat-assuming` (with cube literals as assumptions) for 647 of its
  1001 checks and follows UNSAT results with **206 `get-unsat-assumptions`** calls —
  every successful consecution check *doubles as a generalization step*: the returned
  core is the subset of cube literals the proof actually needed, so literals are
  dropped wholesale with zero extra queries.
- patronus sets up none of this (it never enables `:produce-unsat-assumptions`) and
  pays **2 fresh queries per literal-drop attempt** (`intersects_init` +
  `rel_ind_check`) in `generalize`. That's why 384 of its 1251 queries are
  current-step-only and why per-clause cost scales with state width — the exact
  mechanism that makes the 16-bit `aman_goel` original intractable for the current
  implementation (~110 queries/clause measured) while remaining routine for Pono.

The clause-quality numbers tell the same story: Pono's learned clauses average 2.8
bit-literals vs. patronus' 3.7 — core-guided dropping generalizes further, and stronger
clauses mean fewer obligations downstream.

### 4. Query discipline: assumptions-only vs. scoped asserts

patronus runs the entire session as one monotone context with 100% `check-sat-assuming`
and zero `push`/`pop` — optimal for bitwuzla, but it is also why the missing
`check_assuming_end` (review Issue C) goes unnoticed: on solvers where
`check-sat-assuming` is emulated by `push; assert; check-sat`, the patronus session
would corrupt itself. Pono wraps every query in `push 1 … pop 1` and uses plain
`check-sat` whenever it doesn't need a core (354/1001) — portable by construction.

### 5. Model extraction: word-level vs. bit-level

patronus reads whole words (`(get-value (u@1))`, 2–4 calls per model, 117 total) and
slices bits client-side in `get_bit_level_cube`. Pono queries the solver **per bit**
(`(get-value ((= ((_ extract 0 0) state5) #b1)))`, 484 total). Here patronus has the
better design — one of the few dimensions where it is strictly leaner.

### 6. Trivial-counterexample handling

`trivial_input_fail`: patronus 3 queries vs. Pono 2. Pono's IC3 base does the 0-step
(`F₀ ∧ bad`) and 1-step (`F₀ ∧ T ∧ bad'`) checks and stops; patronus does `init_check`,
the frontier query, and then a third `intersects_init` to confirm the frame-0
obligation that its descent machinery created. One extra query on trivial traces —
negligible, but it shows the descent path engages even for depth-1 counterexamples.

## Interpretation of the totals

The raw ratios (2.0× on simple_fail, 1.25× on aman_goel_4bit) understate the gap,
because patronus' overhead is concentrated in `generalize` and scales with cube width:
at 3-bit/4-bit state widths the 2-queries-per-literal loop is affordable; at 16 bits it
is the difference between converging and hanging (measured earlier: ~5 clauses/sec,
monotone but unbounded). Pono's per-clause cost is essentially width-independent
(one core harvest per UNSAT).

## Recommendations, in impact order

1. **Core-based generalization**: enable `:produce-unsat-assumptions`; in
   `rel_ind_check`, pass the cube's NXT-step literals as individual assumptions and
   harvest `get-unsat-assumptions` on UNSAT — the core replaces most of the
   literal-drop loop. (The `SolverContext` trait needs a
   `check_sat_assuming_core`-style entry point.)
2. **Predecessor shrinking**: full 2·width-literal predecessor cubes are the other
   width-scaling cost; shrink with the same core mechanism (or ternary simulation)
   before enqueuing obligations.
3. **Garbage management**: retired/subsumed clause assertions accumulate gated-but-
   permanent; adopt Pono's periodic rebuild (`reset-assertions` + re-assert live
   clauses) once clause counts get large.
4. **Portability**: pair `check_assuming_end` (Issue C) or require native
   `check-sat-assuming` — Pono sidesteps this class of bug with per-query scopes.
5. **Keep** the word-level `get-value` extraction and single-assert-per-clause delta
   encoding — both are cleaner than Pono's equivalents at this scale.
