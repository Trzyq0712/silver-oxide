# 30 — Joins, reachability, and the structural perm collapse

## Purpose

Define the join: merge predecessor heaps/values under **exhaustive edges** so the exit
perm collapses to `1/1` structurally (the whole point), plus feasibility pruning and
dead-block skipping (the Silicon-prune analog).

## Current understanding (decided / measured)

- **The value phi already works** (`build_entry_env`, `reach.rs:193`): `ite(e0,v0,
  ite(e1,v1, … v_last))`, last arm unguarded because edges are exhaustive → no
  fall-through leaf. **The perm must use the same shape.**
- Today the perm instead accumulates as scaled `Σ ite(flag_k,1/1,0)` with a **`0`
  fall-through** → won't collapse → the one tier-4 split. Block joins remove the `0`.
- Each arm already gives back `1/1` (the `(x−p)+p ⇒ x` cancellation works); the join
  only needs to **select among arms under exhaustive edges**, not sum scaled indicators.
- **Feasibility prune / dead-block skip:** a block whose local proves its cube
  inconsistent (`bb_unreach`, same-value nested `unreachable!()`) is `Inconsistent` →
  skip its values/heap. This is Silicon's "prove false, stop" at block granularity.
  Same-value nested dead arms are direct const-fold contradictions (measured trivial).
- **reach.rs cube telescoping** already collapses a full exhaustive cover to `<>`;
  keep the DNF (not materialized) so nested joins telescope (`project_reach_dnf_pc`).

## Perm merge rule at a join (decided 2026-07-26)

The join merges predecessor arm heaps per location. Two cases, both handled by the
`[50]` Σ-ite availability model — a location's perm is a guarded sum over the arms'
chunks, each guarded by its incoming edge:

- **Uniform footprint (give-back):** every arm holds `L` at the same amount →
  `ite(e0, p, ite(…, p))` last-unguarded → collapses to the **constant** `p` (e.g. `1/1`).
  This is the structural collapse; no guard survives.
- **Divergent footprint (risk 6):** `L` held in some arms only → those arms' chunks are
  absent (contribute `0`) → the perm stays a guarded `ite(edge, p, 0)`, i.e. a
  **persistent conditional held perm = U4**. It does *not* collapse to a constant, and
  that is correct — `L` genuinely is held only conditionally.

**Join construction rule:** the merged perm at a location is a **SELECT over the arms'
exit perms under exhaustive edges** — `ite(e0, p0, ite(e1, p1, … p_last))`, last arm
unguarded — **never an additive Σ over the arms.** Uniform locations collapse (idempotent
select); divergent ones keep a `0`-leaf select `ite(edge, p, 0)`.

**SELECT ≠ the `[50]` aliasing Σ (do not conflate).** Two different sums are in play:
- `[50]`'s `avail(x.f) = perm(f(x)) + ite(x==y, perm(f(y)), 0) + …` is the **aliasing**
  sum: **one state**, over maybe-equal addresses, genuinely additive (Silicon's model).
- The **control-flow join** is over **mutually-exclusive arms** → **SELECT**. Summing
  edge-guarded arm chunks (`Σ ite(edge_k, p_k, 0)`) **double-counts** any inherited/
  untouched perm (`p + p = 2p` where select gives `ite(e,p,p)=p`) and rebuilds the exact
  `Σ ite(flag,1,0)` `0`-tower that forces tier-4. Divergence is therefore a **select with
  a `0` leaf** (`ite(edge,p,0)`), *not* a Σ term. The old "union = Σ" framing was the bug,
  not the mechanism.

### Merge collapse mechanics — the guard-granularity result (2026-07-26)

**Mechanism:** a **structural merger outside the e-graph** (see `[40]` "join collapse is
structural") reads the arms' **explicit** perm terms (`[50]`) and dispatches on the closed
pattern set. The identities below describe the *semantics* it realizes — they are **not**
e-graph rewrite rules. The guard-degradation still relies on the merger evaluating in the
join block's context, which assumes the block's own pc = the **common prefix** `X` shared
by all incoming arms (invariant 3). This is load-bearing, not an optimization:

- A chunk's exported perm is guarded by the **full path cube**, not the edge alone:
  `ite(X&&d, p, 0)` from the `d`-arm. If the merge selects on only the edge `d` in a
  context that does *not* assume `X`, the residual `X` inside the guard has unknown truth
  → the `0` leaf **survives** → tier-4. (This is exactly the naive/monolithic failure.)
- Run the merge **in J's local (`X` assumed)** → `X&&d ≡ d` const-folds → the full-cube
  guard **degrades to the edge** → the select collapses. **General principle: a chunk's
  guard folds to `true` whenever the merge block's pc implies it; only the *incremental*
  condition since the chunk's own split survives.** No relative-guard bookkeeping needed.

**The identity (unconditional, all 4 rows):**
```
ite(d, ite(X&&d, p, q), ite(X&&!d, r, s))  ===  ite(X, ite(d, p, r), ite(d, q, s))
```
Under `X` assumed (J's local): `=== ite(d, p, r)`. `q, s` are the **export-elses = 0**
(you don't hold a chunk off its path) → gated out by `X`, never in the result. RHS is a
SELECT on `d` between the two arms' *held* perms `p, r` — **never `p+r`, never keyed on
`X`** (dropping `d` is wrong: `(d=F,X=T)` is `r`, not `p`).

**Symmetric hot case (`p==r ∧ q==s`), realized structurally:** the merger recognizes both
arms carry the same amount and emits `ite(X, p, q)` **directly** — it never builds the
4-way intermediate. `p==r`/`q==s` tested by structural eq with leaves compared via e-class
`find()`. Dominant path — symmetric give-back / inherited-untouched. Give-back `p=1,q=0` →
`ite(X, 1, 0)`; evaluated where `X` holds → **`1`**. Whole thesis: `d` dies by same-amount
recognition, `X` dies by block-pc, residual is ground `1` — no `0` leaf, no exhaustiveness
proof, no tier-4.

**Read-off, not extract-then-rewrite (the enabler).** The merger reads each arm's perm as
an **explicit term** already sitting on the ghost chunk (`[50]`) — bare `1` for a give-back
because perms are stored as **identity-else reach-guarded deltas** (`ite(P, old±amt, old)`)
and an amount-preserving op collapses `ite(P,x,x)→x` at its smart constructor, leaving the
inherited amount bare. The bare value is **constructed, not derived** (no invariant-1
leak): it is the as-written inhaled/inherited amount surviving a zero net delta, read off
the struct in O(size) — **not** a value proven under the block pc and extracted. Contrast
the value-with-zero-else representation `ite(P, amt, 0)`, on which give-back does *not*
cancel → you'd be forced to widen a materialized guard. The identity-else choice in `[50]`
is precisely what makes read-off yield a bare value here.

**Guard once, never double-guard.** The double-nested `ite(d, ite(X&&d,…), …)` only forms
if perm is guard-wrapped at *export* AND re-guarded at the *join* — same pc twice. The
structural merger applies the guard **once**, from the arms' bare/explicit perms +
provenance, so the inner guard never materializes. This is the `(pc, chunk-map)` join op,
not the generic guarded-fact export.

**Soundness/discharge:** a divergent location can only be *demanded conditionally* (an
unconditional demand on it is a genuine Viper permission error). So exit sufficiency is
`ite(edge, p, 0) ≥ ite(demand_cond, need, 0)` — discharges in the exit local **iff `edge`
and `demand_cond` share an e-class** (join telescoping + T1 flag→condition threading). The
residual (semantically-equal, syntactically-distinct guards) is the **same
exhaustiveness-bridging residue → Z3**. Measured: `divergent.vpr` needs 1 split today and
fails `NO_TIER4` — the identical signature to the enum give-back, confirming it is not a
distinct failure mode. **Rarity:** Prusti routes owned data through uniform result
places, so genuine divergence is uncommon (result-place arms are uniform, not divergent).
- **In-arm perm ADD vs join SELECT.** `project_heap_ternary_join_select`: joins SELECT
  arm heaps; in-arm perm adds go **unguarded** (needs the local scope — inside the block
  the inhale is literal `1/1`). Confirm the split: SELECT at join, unconditional ADD
  inside block.
- **Nested joins** collapse bottom-up (inner → `1/1` before outer sees it). Falls out of
  topo block execution + ghost fork-merge (`[20]`): each merge's combined ids become the
  next join's base, so inner collapses/remaps are visible to the outer.

### Value merge (2026-07-26) — resolves "value vs perm vs heap: unify or separate?"

**Unify the dispatch, split the output medium.** One structural merger, one closed pattern
set, for value + perm + heap. Divergences are only:

| | perm | value |
|---|---|---|
| storage | explicit term (out of e-graph, `[50]`) | **e-graph e-node** (needs congruence / axiom rewriting / triggers) |
| collapse `ite(c,x,x)→x` | smart constructor on the struct | **canonicalize-on-store** at e-node insertion (M0 `V1`) — not saturation |
| scope | whole heap threaded | **live-cone only** (merge a value iff live past the join; else drop) |

Values are the **easy** side — two perm complications are absent: (1) **no additive
hazard** (values are never summed → SELECT is unambiguous); (2) **no `0`-leaf /
exhaustiveness** (every live arm has a value → the exhaustive-edge phi has no fall-through
— why "the value phi already works" today). Same reach-telescoping, same dead-arm Route 1,
same idempotent collapse.

**Join reads threaded reaching-defs, not immediate-pred outputs.** Values are ghost
e-classes; the env (`var→ghost-e-class`, a `[10]`/`[20]` deliverable) is **inherited +
overridden** in topo order, so a value defined at a dominator and untouched in the arms is
already bound to its base e-class on every arm — **no up-DAG search**. The join reads each
arm's env binding:
- **same id all arms** (untouched / same recompute) → collapse, no phi. Covers the
  "source higher up in the DAG" case for free.
- **redefined on ≥1 arm** → textbook SSA phi: `ite(edge, vA', vB')` over the **remapped**
  (`[20]`) arm values; un-redefined leaves = the inherited base id.

**Both arms overwrite `x`:** `x_J = ite(edge_A, vA', vB')` where `vA'`, `vB'` are the arm
values remapped into the combined ghost (`[20]` re-canonicalization). If they re-hash-cons
equal → collapse. **Id stability** is the `[20]` remap: base ids pass through, arm ids
remap, combined ids are stable downstream; provenance/recipes remapped too (U6).

**Divergent definedness:** a value live past the join is defined on every reaching arm by
CFG well-formedness (Prusti SSA) → no "undefined" leaf; genuinely one-sided values aren't
live past the join → dropped by the cone. Adversarial test: a malformed CFG reading a
local undefined on some incoming arm → merger must not fabricate a value.

**Heap-dep / snapshot values** merge as values (SELECT) but their leaves carry
perm-derived conditions (`present = 0 < Σ-ite(perm)`) → conditionality tracks the
underlying perm merge = **U4** (`[50]`, `perm_cycle_explanation`); dissolves in-block,
persists at joins.

## Sketch (to fill)

- [ ] Join algorithm: inputs (predecessor exit heaps + edge guards), output (entry
  heap), on the N=4 enum join. Show the exit perm folding to `1/1`.
- [ ] Partial-footprint case worked (a match where arms hold different locations).
- [ ] Dead-block detection + skip in the block executor.

## Risks

- **Footprint divergence** is the one place the structural collapse can't apply →
  residual `ite(edge, p, 0)`; nested divergence multiplies. Needs either a proof (Z3 as
  escape hatch) or a guarantee it doesn't arise in Prusti output. **Highest-value test:
  a Prusti-generated nested-`&mut` case** (not in the matrix yet; needs Prusti).
- Getting "exhaustive edges" from the CFG under Prusti's flag reification — may need
  T1-style flag→cube recognition so the join sees the arms as the exhaustive cover.

## Depends on / feeds

Depends on `[10]`, `[20]`, `[50]`. Feeds `[40]` (which rules the join still needs).

## Status

perm-merge (structural, no rewrite rules), footprint divergence, **value merge** (unified
dispatch / split medium / reaching-defs / id-stability via `[20]` remap), and **dead-arm
Route 1** all **decided** (2026-07-26). Remaining to sketch: the full one-pass join
*algorithm* (value + perm + heap together) and dead-block-skip wiring in the block executor.
