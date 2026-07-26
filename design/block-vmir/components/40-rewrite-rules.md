# 40 — Rewrite-rule set for block-based discharge

## Purpose

Decide which rules survive block-based, and assign each to the tier registry
`local-only | reductive | instantiating`. Central sub-question the supervisor flagged:
**do we still need the distributive `lt-ite` (and `eq-ite`) rules? What are they
crucial for right now?**

## Current understanding (decided / measured 2026-07-25)

Rule inventory in `src/verify/rewrite.rs`. Measured on the enum family with the built-in
ablation flags (`SILVER_OXIDE_NO_LTITE / NO_EQITE / NO_DISTRIB / NO_TIER4`):

- **`lt-ite`** (`rewrite.rs:481`, fused `LtIteDistributeApplier`): pushes `<` through an
  `ite` tower to the leaves in one application. Its own doc: *"CFG linearization encodes
  a conditional inhale/exhale as a scaled permission `c ? p : 0`, so the permission ≥ 0
  obligation is a `<` applied to an ite tower."* Measured:
  - `NO_LTITE + NO_TIER4` on `enum_clike__mut_through_match` → **FAIL "permission may be
    negative"** — i.e. lt-ite's crucial job **right now** is the **`perm ≥ 0`
    side-condition on scaled perms**.
  - `NO_LTITE` alone → tier-4 splits **1 → 5** (tier-4 compensates for sufficiency); so
    lt-ite is also a **sufficiency perf-multiplier**, not strictly load-bearing there.
  - The real Prusti mut case passes without lt-ite (tier-4 covers); the flat `gen_8`
    generator does **not** (`NO_LTITE`/`NO_DISTRIB` → FAIL). Generator ≠ Prusti shape.
- **`eq-ite`** (`eq-false-then/else`, unit propagation from disproven `==`): `NO_EQITE`
  not load-bearing on these cases. Keep as suspect-for-removal.
- **`ite-reduce`** (`rewrite.rs:530`, fused): the terminating simplifier; ~70% of
  historical search cost lived in its unfused form. **Reductive tier, stays** — it is
  what collapses `ite(c, x, x)`, `ite(true/false, …)`, nested-same-`c` towers (the
  same-value nested-match collapse rides this).
- Algebraic identities (`add-zero`, `mul-one`, `mul-zero`, `sub-self`, `add-sub-cancel`,
  `lt-irrefl`, `div-one`) and `eq-true-union` / `eq-refl` / congruence: framing core.
  The give-back cancellation `(x−p)+p ⇒ x` lives here (`add-sub-cancel`, `c883f17`).

## The lt-ite thesis under block-based

The scaled `c ? p : 0` permission is a **linearization artifact**. Inside a block that
assumes its pc, an `inhale acc(x.f, p)` contributes **unconditional literal `p`**, so
`perm ≥ 0` is `p ≥ 0` over a constant → trivial `ConstFold`, **no lt-ite**. Therefore
lt-ite's primary reason to exist **evaporates** under block-based. Residual `<`-through-
`ite` demand:
1. **Conditional held state inherited through joins** — a phi-selected perm
   `ite(edge, p_a, p_b)`; a comparison against it may still want a bounded descent.
2. **Expression-level WD guards** (shallow, bounded).

**Hypothesis:** lt-ite demotes from a saturation rule to (at most) a bounded reductive
descent, or is removed entirely once M3 makes in-block perms unconditional. **Must be
measured on block-based**, not assumed. Same for eq-ite (likely removable earlier).

## Join collapse is STRUCTURAL, not a rewrite-rule set (decided 2026-07-26)

**There are no perm-merge rewrite rules.** The join is resolved by a **structural merger
outside the e-graph** that reads the arms' **explicit** perm terms (`[50]`) and dispatches
on a finite, closed set of join shapes. Reasons: control-flow joins have a small closed
shape set (direct dispatch ≫ e-match search); it's deterministic / bounded / O(size)-per-
join (no saturation, no scheduler, no rule registration); and the collapse happens at
construction so the mess never enters the graph (feeds the growth win). This **supersedes**
the earlier "fused symmetric-join reductive rule" idea — that framing (fire an e-graph
rewrite `ite(d,ite(X&&d,p,q),ite(X&&!d,p,q))⇒ite(X,p,q)` inside the local) is dropped.

**Closed pattern set the merger handles** (the identities still describe the *semantics*;
the *mechanism* is a structural pattern match, not a rewrite):

| pattern | action | result |
|---|---|---|
| same amount both arms (give-back / uniform) | collapse | `p` |
| inherited-untouched (same term ref) | collapse | inherited term |
| reachable + unreachable sibling | take live arm, guard by reach(J) (telescoped) | `ite(X, p, 0)` |
| divergent (held in some arms only) | keep select | `ite(edge, p, 0)` |
| different amounts, both live | keep select | `ite(edge, p, r)` |

**What the merger queries the e-graph for** (cheap, NOT saturation):
- **"same amount?"** — structural eq on the explicit perm term, **leaves compared by
  e-class `find()`** (near-O(1)). Not a value-extraction walk.
- **deadness** — the block-local inconsistency flag (a bool).
- **guard-condition compare / exhaustive cover** (`d`/`¬d` → `X`) — reach-DNF telescoping
  (`project_reach_dnf_pc`) + congruence `find()`.

**Soundness posture — conservative by construction:** a leaf equality that is *not*
congruence-immediate → merger returns "not equal" → keeps the honest `ite(edge,p,r)`
select. **Never collapses unsoundly.** May miss a collapse full saturation would find — but
the target cases are congruence-immediate (give-back nets to the same `Const`; dead-arm is
structural telescoping). The rare semantic-equal-but-syntactically-different residual falls
through to the **local e-graph / Z3 escape hatch** (`[30]` exhaustiveness-bridging residue).
Layered: **structural-merge first, e-graph/Z3 for residual only** — the hot path never
saturates.

**Verdict impact:** removes the `perm ≥ 0`-over-`Σ`-tower obligation *and* the whole
perm-merge rewrite class. The tower never forms — the merger builds the collapsed form
directly. Strengthens the `lt-ite` demote/delete hypothesis at M3 (§lt-ite thesis).

## Open decisions

- Final tier assignment for every rule (table to build): local-only / reductive /
  instantiating / delete.
- Does the structural join (`[30]`) fully remove the `perm ≥ 0`-over-tower obligation,
  or does the phi-selected conditional perm reintroduce a (bounded) need for lt-ite?
- `merge_ite_sum` / `merge_summands` / `flatten_plus` (`context.rs`): the hand-rolled
  partition collapse and its **code-smell** plumbing (self-reference heuristic, budgets,
  dual-use, residue accretion). Block joins should make it **unnecessary** — confirm and
  delete, don't port.
- Tier-4 (`split_prove`/`split_tree`/`SPLIT_BUDGET`): dropped, replaced by tier-3.5
  non-forking ite-descent (`f55f6c0`, already present) + Z3 escape hatch only for
  footprint-divergence residue (`[30]`).

## Sketch (to fill)

- [ ] Full rule → tier table with the survive/demote/delete verdict + the measurement
  backing each.
- [ ] The minimal rule set that discharges the enum family under block-based (predict,
  then verify by ablation once M2/M3 exist).
- [ ] Re-run all ablations at M3 and diff against this doc's current numbers.

## Risks

- Deleting a rule that's load-bearing on a shape not in the current corpus (generator vs
  Prusti divergence already seen). Gate every removal behind the full suite + corpus,
  Z3-independent, measured.

## Depends on / feeds

Depends on `[20]` (tiers), `[30]` (what joins remove). Feeds `[70]` (M4 rule diet).

## Status

seeded (measured) — the rule→tier table is the deliverable; verdicts firm up at M3.
