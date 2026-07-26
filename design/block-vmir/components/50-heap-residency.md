# 50 — Heap residency across blocks

## Purpose

Decide where a chunk's `value`/`perm`/`addr` e-classes live when the heap threads across
block boundaries, and how heap mutation reflects into the ghost. Flagged in
`why_switch_architecture.typ` as *"undesigned — where the bookkeeping will hurt."*
**Largely resolved 2026-07-26** (discussion below); the residency model + the
consume-under-aliasing rule are now settled.

## Resolved model

**Heap is ghost-resident; locals only read + prove; construction = ghost, proof = local.**

- The symbolic heap (`heap.rs::Heap`, chunks partitioned by `LocationKind`) lives in the
  **ghost**. `addr` is a `FuncApp` spine → stable across the ghost by structural hashing
  (aliasing via congruence, but only for **globally-true** equalities).
- Heap **ops** (acc / fold / unfold / inhale / exhale / join) construct values
  structurally from ghost inputs (recipe / `FuncApp` / `proj` / `cons` / `ite`) — that
  construction is ghost-side. A **local** (per block, seeded from the live cone, assumes
  the block pc) only **discharges obligations** — it never creates persistent heap state.
- Therefore **nothing goes local→ghost as derived state.** The only things crossing the
  boundary are (a) as-written asserted/assumed **propositions**, guard-wrapped by the
  block pc, and (b) the ghost heap map itself, whose component ids are always
  ghost-constructed. This dissolves the earlier "U1: re-extract the value" and "U2:
  heap-map-as-state" worries — there is no local-born heap value to extract.

### Permission is a guarded sum (Silicon's Σ-ite), not a single owner

Perm available at a location = **guarded sum over the aliasing chunks**:
```
avail(x.f) = perm(f(x)) + ite(x==y, perm(f(y)), 0) + ite(x==z, perm(f(z)), 0) + …
```
This is Silicon's `perm(loc) = Σ ite over same-id chunks`; the `heap.rs` vec-per-location
shape was built for exactly it ("the lazy Σ-ite permission model"). **The alias lives
only in this sum and in the sufficiency proof — never in a chunk merge and never in the
debit.**

> **This Σ is the *aliasing* sum (one state, maybe-equal addresses) — NOT the control-flow
> join.** The join across mutually-exclusive arms is a **SELECT** (`[30]`), never a Σ:
> summing edge-guarded arm chunks double-counts inherited perm and rebuilds the tier-4
> `0`-tower. Keep the two mentally separate — same `ite` machinery, opposite monoid
> (`+` within a state, select across arms).

### Perm is an EXPLICIT term, not an e-graph e-class (decided 2026-07-26, supervisor-endorsed)

A chunk's permission is a **first-class structured term held on the `Chunk`, outside the
union-find** — a small perm AST (`Const · Sum · Scaled · Ite(cond, then, else)`), where
**values are explicit** but **guard/cond leaves are e-class refs**. Motivation: if perm
lived *in* the e-graph, reading it gives an e-class **handle** but not its shape — knowing
"is this bare `1`?" would need const-fold-data (only if already folded), a representative
**extraction (walk)**, or **saturation** to canonicalize. Give-back residue `ite(P,old,old)`
is `1` only *after* ite-reduce fires; at read time it's a different class. That
saturation-dependence is exactly what the redesign kills.

**The two-role split** (the e-graph was overloaded; separate them):
1. **Perm-term canonicalization → OUT of the e-graph**, into deterministic **smart
   constructors** on the perm struct (`const-fold`, `ite(c,x,x)→x`, `(x−q)+q→x`,
   identity-else collapse), applied at construction. Bounded, terminating — block structure
   + identity-else make it local, so **no budgets** (unlike today's `merge_ite_sum` /
   `flatten_plus` / `merge_summands` imperative-unbounded plumbing).
2. **Obligation discharge + condition congruence → STAYS** in the local e-graph
   (sufficiency `avail ≥ need`, aliasing `x==y`, guard-implication `X⟹d`).

**Cost model this buys:** read perm shape = O(size) struct walk (deterministic); build join
select = O(1) term-ref plug; compare two guard *conditions* = union-find `find()`
(near-O(1)); **extract-a-value-from-a-raw-e-class = the walk we never do**. `ite(c,x,x)→x`
is trivial structural `x==x`; dropping `d` under `X⟹d` is a congruence query on the
*condition*, not a value extraction.

**Refines `[40]`'s "delete `merge_ite_sum` et al.":** delete the *heuristic/budget
plumbing*; **keep** the *explicit perm representation* with bounded smart constructors. The
join **structural merger** (`[30]`/`[40]`) reads these explicit terms and resolves merges
by pattern dispatch — no perm-merge rewrite rules. Old = explicit-but-unbounded; new =
explicit-and-bounded.

### The consume-under-aliasing rule (the crux, U3)

An exhale `acc(x.f, needed)` where `x==y` holds only locally (branch literal *or*
`assume`, or congruence-derived from as-written roots):

1. **Which chunks?** Group partition → only `.f` chunks are candidates. Per candidate,
   probe address-equality to `x.f` under the local's state (this is exactly
   `chunk_under_pc`, declaration.rs:250/410): `f(x)` yes (syntactic), `f(y)` yes (via
   `x==y` congruence), `f(z)` no (`z==x` unprovable). Congruence **is** the touched-set
   oracle; nothing tracked separately.
2. **Sufficiency:** prove `avail(x.f) ≥ needed` in the local (alias resolves the guards).
3. **Consume:** debit **only the syntactically-demanded chunk** `f(x)` by the **full**
   `needed`, **guarded by the block reachability pc `P`**:
   `perm(f(x)) := ite(P, old − needed, old)`. **Do not split, do not touch `f(y)`, never
   merge in the ghost.** Inside the block the debit looks unconditional (pc assumed); its
   ghost-resident form is pc-guarded (reconciled at block exit / join — the
   heap-ternary-join mechanism).
4. **Correctness without attribution** — later reads re-sum with the alias guards:
   `avail(y.f) = perm(f(y)) + ite(x==y, perm(f(x)), 0)` → 0 under alias, 1/2 without;
   `avail(x.f) = ite(P, −1/2, 1/2) + ite(x==y, 1/2, 0)` → 0 on the reachable arm.
   "How much from each" is a **non-question** — only the sum has meaning.

### The ≥ 0 invariant, refined

- **Per-chunk ≥ 0: dropped.** A chunk can be individually negative (`f(x) = −1/2`);
  meaningless in isolation, sound because only the sum is read.
- **Per-location-sum ≥ 0: kept, but "at every *reachable* state," not syntactically.**
  A syntactically-negative sum can only occur on an arm that is **dead**: for a branch
  alias the negative arm is `P ∧ ¬(x==y)` with `P = (x==y)` → contradictory; for an
  `assume` alias, `¬(x==y)` contradicts the assume → dead. **Requirement:** perm /
  sufficiency checks must run inside a local carrying the block's pc + assumes, so the
  dead arm is seen as dead. (Already how the current system treats perm terms.)
- **Retention without the alias** is encoded in the guard, read per continuation: branch
  → `x≠y` never took the exhale path → `f(x)` keeps full `1/2`; `assume` → `x≠y` is a
  dead state → N/A. No separate retention decision.

### `old` heaps: unchanged mechanism, new threading (2026-07-26)

`old` is **not** a new approach under block-based — I checked the code and it already works
this way. Today (`pure_exp.rs:17` `OldHeaps{ baseline, labeled }`, `:868`) an `old`-heap is
a captured `HeapVal` — `baseline` = post-requires-inhale heap (unlabeled `old`), `labeled`
= `{label L → heap captured at L}` — and `old(e)` re-reads `e` with `HeapCtx.value/perm`
swapped to that frozen heap. `old(f(x))` for heap-dep `f` swaps to the old heap, so `f`'s
`Snap` reads the **old** heap; the body `FromSnap` reconstructs the old footprint. Whole
heap-state is captured per label (no per-field pre-scan); the only static bit is *which
labels* to capture (those under `old[L]`, plus baseline).

**"How do we have access?" — checked, not assumed.** `eval_snap` (`declaration.rs:1832`)
runs a **non-consuming footprint-sufficiency check** (scratch subtraction clone, discarded
— *functions frame, they don't consume*) against the handed heap; the resource boolean is
asserted over the read values. For `old(f(x))` the handed heap is the old heap → access iff
the old heap's footprint suffices; pre-token exported as a fact only on success (`:1897`).
No writeback → doesn't perturb the current heap.

**Block-based delta = threading only.** Captured `old` `HeapVal`s become ghost objects
under the same discipline as everything else:
- **liveness roots** — kept alive from capture to last `old`-use (they are not current
  temps; explicit roots, `[20]`).
- **remap targets** — method-entry baseline = pre-split base → **identity** remap;
  `label L` mid-branch → **fork-remapped** (`[20]`); divergent if one-armed.
- **local-seed inputs** — the old heap's chunks must seed the local that evaluates
  `old(f(x))`, so `eval_snap`'s sufficiency runs there. Non-consuming → no give-back
  interaction (clean with the block model, no negative-perm writeback).

Value stability closes it: the old-`Snap` is a FuncApp over **current args** `x` (stable)
+ **old chunk values** (stable via remap) → congruence-coherent wherever the same `old(e)`
appears. `old(perm(x.f))` (rare) needs the captured explicit **PMF** term, not the value
FVF — capture a frozen perm term only if a contract reads old *permission*.

### Ties to other components

- Alias from an **`assume`** has no sibling cube → its `ite(x==y,…)` guard never
  telescopes → the perm **persists as conditional held state** = **U4** (`[40]` lt-ite
  residual). The ghost must retain the `pc ⟹ x==y` proposition so successor locals
  re-establish the alias.
- Alias that **over-saturates** a bounded location (`1/1 + 1/1` under `x==y` on a
  field) → field-perm bound fires → **inconsistent local → dead block** = **U7**.
- Bounds / non-aliasing axioms already operate on the location **sum**
  (`assume_location_axioms`) → consistent with this model as-is.
- **Heap-dep snapshots inherit U4 through presence flags** (`[20]`): a `Snap` builds its
  value from `present = 0 < Σ-ite(perm, slot)`, so an inherited-conditional perm makes the
  snapshot *value* conditional — the `m_point_step` presence-guard cycle
  (`perm_cycle_explanation.md`). Dissolved in-block (perm concrete → `0 < perm`
  const-folds), persists at joins as U4.

## Remaining open decisions

- **U4 quantification:** how often does Prusti output leave a location held under only
  some incoming edges (persistent conditional perm)? Measure; decides whether a bounded
  `<`-through-`ite` descent survives in `[40]`.
- **U5 seeding granularity:** which chunks the live cone imports, and whether
  non-aliasing axioms re-run over the imported subset (miss a frame) or the whole heap
  (O(chunks²)/block). Unresolved.
- **U6 recipe survival:** does `Chunk.recipe` (Deref-purify / cert graft provenance)
  survive a local↔ghost round-trip, or degrade to `None`? (join-merged values are
  already `recipe: None`, built ghost-side — fine; written/fold/unfold values are
  recipe-backed — confirm they persist.)
- **fold/unfold across blocks (U8):** intermediate chunks' `proj`/`cons` values depend
  on U6.

## Sketch (to fill)

- [ ] Worked `*v` (`p_Param`) chunk trace through `arm_0 → wb_0 → join` + the give-back
  cycle, annotating id-space and pc-guard at each boundary — validates the model
  end-to-end and reveals whether `Chunk` needs a new field.
- [ ] A two-chunk aliasing consume worked in full ghost-term form (the Q1/Q2 numbers).

## Status

resolved (residency + consume rule) — remaining opens are U4/U5/U6 measurements, not
design unknowns. The worked trace is the next deliverable.
