# 20 — Verifier: local-per-block + ghost archive

## Purpose

Define the two-tier e-graph: a **local** per block (assumes pc, all rules, discarded)
and a persistent **ghost** archive (congruence + reductive + unconditional
instantiation only). Where obligations discharge; what crosses the boundary; how
functions/resources fit.

## Current understanding (decided / measured)

- **Local:** seeded from the ghost's **live cone** (terms reachable from current
  store/heap; `Chunk.recipe` provenance is most of the extraction machinery). Assumes
  the block cube **unconditionally**, runs **all** rules. All the block's obligations
  discharge here — flags/discriminants are constants, arm-local obligations trivialize.
  Discarded at block exit. Quantifier instantiations live and die here → fixes
  branch-pollution unsoundness.
- **Ghost:** today's graph, demoted. No heavyweight search. Congruence + `ConstFold` +
  **strictly-reductive** rules (RHS references only existing subterms) + **instantiation
  of unconditional foralls / function-post-facts** only. All ghost rules trigger off the
  **dirty set** at export time (cost ∝ export size, never ∝ ghost size).
- **Export = propositions, not state** (invariant 1). Wrapped with the block pc. Nothing
  the local *derived* crosses. FuncApp spines preserved automatically (terms export as
  written).
- **Export base set (decided 2026-07-26): only Viper-explicit *assumes*.** `assume`
  statements + inhaled contract booleans cross. **Asserts do NOT export by default**
  (enablable flag) — an assert is a *check*, not new knowledge; its content traces to
  assumes + reductive/join derivation, which the ghost reconstructs. Everything else is
  re-derivable.
  - *Memo caveat (corrected):* the current engine's `record_proven` (context.rs:610)
    unions `imp == true` — a **verdict memo** for re-proving the *identical* obligation,
    **not** propagation of assert content. Only an **empty-pc** goal unions `goal == true`
    (productive: collapses arg classes via `eq-true-union`); conditional goals memoize the
    *implication* (+ consolidate into `true`). So block-based loses nothing here by not
    exporting asserts — today's engine doesn't propagate their content either.
- **Heap is ghost-resident; construction = ghost, proof = local** (see `[50]`): heap ops
  build values structurally from ghost inputs; the local only proves. The heap map
  crosses as ghost state whose ids are always ghost-constructed.

## Resolved: functions & resources propagation (2026-07-26)

**Functions and resources use the *same* discipline as heap chunks — the local proves,
the ghost holds a guarded proposition that "looks wrong" in isolation, and the ghost's
own replay produces the consequence.** The existing pre-token / guarded-fact machinery
(`cert.rs::Fact`, `rewrite.rs::replay_facts`, `FuncRegistry::pre_token`) *is already this
pattern*; the local/ghost split just names the tiers.

Mapping:
- **Fact production = local** — prove the function/resource body's `Assert`s under
  `pre ∧ block-pc`.
- **Fact storage = ghost archive** — `FunctionDefinition` / `ResourceCertificate`,
  computed once at declaration, **success-gated** (facts install only if the callee
  verified). Recursive post-facts keyed on the limited twin `f'` are ghost-resident from
  body-entry (induction), available in every block's local seed.
- **Replay = ghost instantiating tier** at the consuming site, keyed on the `f(args)`
  anchor. `replay_facts` becomes a **ghost-tier rule** (it already is morally —
  congruence-aware, keyed on a written symbol).
- **The "looks wrong" ghost artifact = the opaque pre-token** `R#pre(args,s)`, assumed
  true under pc, never provable in the ghost — the exact analog of a negative per-chunk
  perm (`[50]`). Both are unjustified in isolation, sound because gated by pc and
  **stamped by a local check that actually passed** (`eval_snap` stamps only where the
  `Snap` sufficiency check succeeded; no stamp on failure → ghost never assumes an
  unjustified token).

Two refinements that keep it airtight:

1. **Only the stamp crosses local→ghost, not the consequence.** The local exports the
   token stamp `pc ⟹ R#pre(args,s)` (an as-written/assumed proposition, like
   `assume x==y`) and the `f(args)` anchor term — **not** the derived post-fact φ. The
   ghost re-derives φ via its instantiating tier on the anchor. Invariant 1 intact.
2. **Heap-dep = basic-heap sufficiency, and simpler — with one asterisk.** The `Snap`'s
   precondition check is footprint sufficiency, **exhale-shaped but non-consuming**
   (fractional read), so it is exactly the `[50]` sufficiency proof with **no debit** →
   no negative-perm writeback. *Asterisk:* the snapshot value is built by reading the
   perm-sum into presence flags (`present = 0 < Σ-ite(perm, slot)`), so an
   **inherited-conditional perm (U4) propagates into the snapshot value** — precisely the
   `m_point_step` presence-guard cycle (`Lt(0/1, perm)`, `perm_cycle_explanation.md`).
   Block-based **dissolves** it in-block (perm is concrete under the assumed pc, so
   `0 < perm` const-folds) but it persists at joins as U4. So "no different" holds for the
   *check*; heap-dep snapshots merely inherit U4's conditionality through presence flags.

Bonus that falls out: this **fixes the "guarded facts don't cross a branch" known
limitation** for the in-scope case — a call under branch pc `P` runs in a block that
*assumes* `P`, so the token guard resolves and replay fires (same reason block-based fixes
exhaustiveness). It correctly does **not** globalize a branch-local fact: if only one arm
established φ, the join keeps it `P ⟹ φ`.

**Cert grafting** = re-adding a resource's globally-true proven facts into the consuming
local (id-translated on re-add, export guarded by the call's pc). Certs are proven
caller-agnostic → safe to graft into any local. Same id-translation pattern as the heap;
no new seam.

**Unfold should propagate like a function post-fact (decided direction 2026-07-26).**
`eval_unfold` (declaration.rs:1782) today is a **heap op**: consume the predicate chunk,
*produce* body field-chunks valued `unwrap(proj_i(s))`, guarded by pc. The exposed
body↔snapshot equalities are therefore **heap state** (ghost-resident, carried forward —
`[50]`), **not** a keyed replayable fact — so after a `fold` (field chunks gone) a
downstream block must **re-unfold** to recover the relationship. Fix: expose the
predicate's **body↔snapshot relationship as a guarded replayable fact keyed on the
predicate snapshot** (its defining axiom), uniform with function post-facts and
re-derivable on demand (fits "everything else re-derivable"), so the local's discarded
unfold work isn't lost and no re-unfold is forced. This strengthens propagation
uniformly: functions, resources, and unfolds all become keyed guarded facts replayed by
the ghost tier.

## Resolved: ghost fork / merge + id remap (2026-07-26)

**Two-merge taxonomy — only one merge exists; the other is banned:**
- **local ↔ local: NEVER.** Per-block locals hold throwaway derived state under a
  contaminating pc; unioning them *is* the monolithic coupling this architecture kills.
- **ghost fork-union at joins: REQUIRED** (invariant 2). Branch ghosts **fork** for
  isolation; the join is a **commutative delta-union**.

**Why fork (the branch-ordering guarantee).** Run arms on one shared ghost and arm A's
guard-wrapped additions (+ any congruence they trigger) are visible while arm B reasons →
B depends on A running first → order dependence. Fix: at the split **fork the ghost
per arm** (COW delta-layer over the shared base — cheap, not a copy; supersedes the
"deep copy, ghost is small" open note). Each arm executes on its fork **blind to
siblings**; the join merges the forks.

**The merge is order-independent by construction:**
- deltas = **guard-wrapped globally-true facts** + **ghost-constructed (hash-consed)
  nodes** → set-union commutes; hash-consing + egg congruence closure are confluent →
  same classes/equivalences whatever the order. So `merge(A,B) = merge(B,A)` *semantically*.
- one residual **syntactic** artifact: phi nesting `ite(e0,v0,ite(e1,v1,…))` follows arm
  order → **pin a canonical arm order** (stable key: block id / canonical edge form) so
  the merged graph *shape* is deterministic too. Distinguish: soundness-order-independence
  (free) vs syntactic determinism (needs the pin).

**Id stability = structural re-canonicalization at merge.** Forks have independent id
spaces for their **deltas** (isolation). Merge **re-hash-cons each fork's delta into the
combined ghost**, producing a per-fork **remap table `fork-local id → combined id`**.
- **Pre-split (base) nodes** pass through **identity** (shared COW base) — this is how
  "defined higher up" values keep stable ids and stay visible with no work.
- **Arm-constructed nodes** get combined ids via the remap; combined ids are the
  persistent substrate downstream → stable.
- **Collapse and id-stability are the SAME mechanism:** both arms constructing the
  structurally-identical value (`f(y)+1`) re-hash-cons to the **same combined id** →
  the phi collapses with no node. No separate equality prover needed for the construction
  case — confluent hashing decides it.

**Apply the remap to everything live-past-the-join, and only that:** live **env
bindings** (`var→id`), **heap chunk values** (`[50]`), and **provenance/`Chunk.recipe`**
(U6 — or it dangles). Scope to the **live cone** — arm-local values dead past the join are
dropped, never remapped → merge cost **O(live)/join** (the go/no-go gate). The remap is
**transient per-join** (used to fix up bindings/heap/recipes, then discarded); nested joins
**compose** — each merge's combined ids become the next join's base. No global remap.

**Adversarial tests:** (a) **remap totality** — an arm-defined value referenced by a live
recipe must be remapped, not dropped (else dangling fork-local id downstream); (b)
**canonical arm order** — two traversal orders must yield the same merged node.

**Value-stability principle (not engineered separately — derived).** Identity = structure:
the ghost's **structural hash-consing** means same-structure ⇒ same e-class. Given that,
stability follows from **one enforced invariant, remap-totality**: base (pre-split) values
are identity-stable forever; a branch value's id changes exactly once (fork→combined at its
merge) and the remap moves **every** live reference (env + heap + snapshot + recipe) with
it, atomically. So "stable" = "id is a function of structure, and the single id-change at a
merge is total." Everything downstream that needs coherent identity — aliasing, snapshots,
`old` — reduces to **FuncApps over stable e-classes resolved by congruence**, so their
correctness collapses to remap-totality. `old`-heaps (the captured `HeapVal`s, `[50]`) join
the **liveness roots** and **remap targets**: method-entry baseline is a base node
(identity-stable); a mid-branch `label L` is fork-remapped. The `old(f(x))` sufficiency
check (`[50]` `eval_snap`, non-consuming) then runs in a local seeded with that old heap.
**Adversarial test:** `old()` in a postcondition after a `match` that overwrites the var in
the arms → the old-value stays base-stable while the current value is phi'd/remapped; both
resolve at the exit.

## Open decisions

- **Live-cone extraction mechanics.** **For now: DON'T. Plain-clone the whole ghost as the
  local seed** (decided 2026-07-26 — try-simple-first). Sound because the ghost holds only
  guard-wrapped globally-true facts (invariant 2): an other-branch fact `pc_other ⟹ φ`
  stays guarded under this block's pc → vacuous, no pollution; the only thing that must not
  leak (the local's quantifier instantiations) dies with the discarded local. So
  clone-whole-in / discard-out is correctness-complete. Likewise **remap all fork deltas**
  at merges (don't scope to live refs) for now. *The key locality survives clone-whole:* the
  monolithic-blowup driver was the graph **accreting derived state**; here the heavy
  derivation is **discarded** with the local and only guard-wrapped propositions export
  (base = assumes), so **the ghost still grows only by the small export delta per block**
  regardless of seed size. *What clone-whole costs* is narrower: per-block **clone + big-
  local search** — a copy/search factor that bites **long programs** (Σ clone over many
  blocks), **not wide matches** (a wide `match` doesn't grow the ghost → clone stays cheap).
  So clone-whole is expected to pass **both** enum gates (correctness *and* N-scaling); the
  long-program clone cost is the separate axis cone-scoping addresses.
  - *Deferred perf step (turn on when the scaling measurement demands):* cone-scoped
    seeding — value cone = **static backward liveness** over temps (reverse-topo)
    **+ explicit `old`/label-snapshot roots**; liveness = roots, seed = **term-cone from
    roots**; heap threaded whole (not cone-scoped — an unread chunk can still frame or feed
    the exit perm-sum). Open then: the recipe/term-cone walk (reuse `cert.rs` /
    `Chunk.recipe`?) + the under/over-seeding completeness cliff (`[60]` risk 5).
- ~~**Ghost fork/merge representation.**~~ **Resolved** (above): COW delta-layer per
  branch (not deep copy) + commutative delta-union + re-canonicalization remap. Perf of
  the layer representation vs base+scratch memo (`7eec230`) is a measurement, not a design
  unknown.
- **Incrementality of the ghost.** Reductive/instantiate pass over the merged dirty set
  only. Needs a merge-delta stream (also the Z3-mirror sync source if Z3 lands).
- **Recipe survival through the local↔ghost round-trip** (`[50]` U6) — does `Chunk.recipe`
  survive for Deref-purify / cert graft, or degrade to `None`?

## Risks

- **Export-selectivity cliff** (`[60]` risk 5) — under/over-export. The principled base
  set + re-derivation fallback is still undesigned. The load-bearing remaining risk here.
- **Inconsistent locals** must export nothing but their guard's falsity (no value
  collapse leaking to ghost).
- **Matching-loop risk moves into the persistent ghost** — a self-feeding axiom now grows
  the archive; needs a hard instantiation budget/depth bound as a design requirement.
- ~~Cert/recipe interaction unmapped~~ — **mapped** (above): certs/functions/resources
  ride the same local-prove / ghost-guarded-proposition / replay discipline. Residual:
  recipe survival (U6) and the graft id-translation details.

## Depends on / feeds

Depends on `[10]` (block IR). Feeds `[30]` (joins), `[40]` (rule tiers, U4 lt-ite
residual), `[50]` (residency, the U4 tie), `[60]` (risk 8 now mostly retired).

## Status

seeded → **functions/resources propagation resolved**; live-cone extraction + export
selectivity remain the open design work.
