# 82 — Correct two-egraph block execution (ground + scratch, ids never cross)

> **Durable copy of the approved high-level plan** (mirrors
> `~/.claude/plans/plan-it-wise-taco.md`, which is ephemeral). This is the
> between-sessions reference for the two-egraph redesign. Approved 2026-07-29.
> Related: `README.md` (invariants), components `20`/`30`/`50`, `81-stage4-*`,
> memory `project_two_egraph_block_model`.

## Context

`generic_option__match_flat.vpr` panics (`unionfind.rs:22 index out of bounds`,
pre-existing on HEAD `9cf90c4`) inside `VerifyContext::tr` (`context.rs:262`):
the per-block **scratch** e-graph translates a **ground** `egg::Id` and hands
egg a child id outside the scratch's id space. Root cause is a *category error*:
`egg::Id`s are indices into **one** e-graph's union-find and are meaningless in
another, yet `tr` imports ground ids into the scratch by walking ground nodes.
The scratch drifts from ground because ground is mutated **outside** the mirror
hooks — `saturate()` runs on every tier-2 prove (`context.rs:643`) and `reduce()`
is called mid-block (`declaration.rs:796/1591/1833/2056/2181/2234`, snapshot-tower
normalization for heap framing) — so `tr` eventually imports/aliases a bad id.

The durable fix is not to patch `tr` but to make the two-egraph model **correct
by construction**: ids never cross between the egraphs; both are kept in sync by
*parallel construction* (a maintained map), not translation. This is the
local/ghost split from this tree (`project_ghost_local_egraphs`), made rigorous.

## Target model (the strategy)

Two e-graphs during a method block, with **disjoint id spaces** that start
identical (clone) and diverge:

- **Ground** = the persistent, *syntactic* record that flows between blocks
  (into successors / joins) and is discarded nowhere. It is **never saturated
  and never proven on during block execution**; it only accumulates nodes that
  are *explicitly* part of VMIR (values, addresses, function-precondition tokens)
  and **guarded** assumptions/heap-effects (under the full block PC), so facts
  from this block never leak to sibling paths.
- **Scratch** = the per-block reasoning e-graph: a clone of ground taken at block
  entry with the block PC assumed, saturated under the full rule set, **the sole
  place any goal is discharged**. Discarded at block exit.

**Invariants (the soundness spine):**

1. **Ids never cross.** After the entry clone, a ground id is never used as a
   scratch id or vice-versa. Sync is by a maintained `ground_id → scratch_id`
   map, populated at *every* mirrored `add`/`union`. Because ground is never
   saturated/reduced in-block, it grows only through mirrored ops, so the map is
   **total** — `tr` becomes a pure lookup (assert on miss, **never import**). The
   OOB path ceases to exist.
2. **Never prove on ground in-block.** All tiers of `prove_under_pc` query the
   scratch. Ground carries no rule-derived ids.
3. **Never saturate/reduce ground in-block.** The six in-block `ctx.reduce()`
   calls (framing normalization) move to the scratch; `prove_under_pc`'s tier-2
   `saturate()` is scratch-only when `in_block`.
4. **Assume placement.** An `assume` fact enters **ground guarded by the full
   PC** (it must not leak to sibling paths) and **scratch unguarded** (the scratch
   already bakes in the block PC; a Viper assume is unguarded except for the
   CFG-implied PC).
5. **Tier-3 (clone-and-assume-extra-PC) only for side-conditions.** The only
   obligations carrying a PC *suffix beyond the block PC* are expression-embedded:
   function-call preconditions and division/`%`-style checks. Everything else
   proves directly on the warm scratch (block PC already assumed).
6. **Statement-level insts carry no extra PC.** `inhale`/`exhale`/`fold`/`unfold`/
   assign operate only at the block-PC level — assert this (a `debug_assert` that
   their inst pc equals the block cube), since they must never be sub-expressions.
   **Known conflict — `unfolding p in e`:** Viper's `unfolding` is an *expression*
   (can sit under a ternary / extra PC), but is currently lowered to a
   statement-level `HeapInst::Unfold`, so it would violate this invariant.
   - **Temporary mitigation (S1):** reject `unfolding` expressions (lowering /
     typecheck error) so no program can hit the violating shape while the model
     lands. Note the regression in the corpus (any case using `unfolding`).
   - **Long-term fix:** encode `unfolding` as a **scoped expression**, analogous
     to the `forall` quantifier (`Symbolic::Forall(RecipeId, captures)`,
     `lang.rs:76`): a scoped node whose body is evaluated with `p` unfolded in a
     *local* scope, with **no** persistent heap mutation and **no** statement-level
     PC. Tracked as its own follow-up.
7. **Heap effects: prove on scratch, record guarded on ground.** A consume proves
   sufficiency on the **scratch heap** (which may hold PC-implied unions — e.g.
   `x.f` and `y.f` each 1/2, unioned to 1/1 under an in-branch `x==y`), while the
   **ground heap** records the effect *syntactically and guarded by PC* — e.g.
   after exhaling 1/1 from `x.f`, ground notes `x.f` as *seemingly* `-1/2` **under
   this PC** (it cannot see the union). Ground heap + ground egraph are what the
   successor/join consumes. (This is the block-heap-consume-model,
   `project_block_heap_consume_model`.)

## Where this lands in the code

- **`EvalState`** (`declaration.rs:19`): `vals: Vec<egg::Id>` stays **ground**
  ids (persistent). The scratch side is the per-block `BlockScratch` + its
  `ground→scratch` map (already exists); we make the map total and drop import.
  `heaps: Vec<Heap>` stays the **ground** heap; a parallel **scratch heap** is
  threaded per block (Stage 2).
- **`VerifyContext::tr`** (`context.rs:262`): delete the import branch
  (`:272–284`); keep only `fast_translate` (map hit / pre-clone identity) and
  **assert** on miss. `fast_translate`'s identity shortcut stays valid because
  ground gains no un-mirrored ids in-block.
- **`prove_under_pc`** (`context.rs:618`): when `in_block`, tiers 1/2/3 run against
  the scratch only (no ground `saturate`, no ground `find` checks). Keep the
  ground-clone tier-3 path for the non-block (function/resource) case unchanged.
- **The six in-block `ctx.reduce()`** (framing): retarget to the scratch (the
  reduce that normalizes snapshot towers for e-class address match must run where
  framing is decided — the scratch).
- **`assume_guarded`/`union` mirror** (`context.rs:239,568`): ground union stays
  guarded; the scratch mirror becomes **unguarded** (union the bare fact with
  `true` in the scratch, not the `Ite(pc,…)` implication).
- **Heap ops** (`heap_subtract`/`heap_union`/`merge_heaps`/framing in
  `declaration.rs`): Stage 2 splits ground vs scratch heaps and adds the guarded
  ground debit.
- **Functions/resources** (no CFG): stay **single-egraph** (no scratch); their
  existing per-obligation ground clone tier-3 is untouched.

## Staging (each stage ends green: `cargo test --lib` + suite + corpus)

- **S1 — id-space separation + crash fix.** Enforce invariants 1–4: `tr` = total
  lookup (no import); in-block proving is scratch-only; no in-block ground
  `saturate`/`reduce` (retarget reduce to scratch); scratch assumes unguarded.
  Gate: `generic_option__match_flat` no longer panics; feature-matrix 27/27
  run; 303 lib green. This is the milestone that kills the bug.
  - **Probe finding (2026-07-29):** rerouting in-block `prove_under_pc` to the
    scratch *before* the tier-2 ground `saturate()` (one edit, reverted) turns 5
    e2e tests red: `conditional_inhale_{true,false}_branch_verifies`,
    `implies_spatial_verifies`, `under_pc_verifies`,
    `heap_dep_post_fires_only_where_the_precondition_bool_holds`. These pinpoint
    obligations that currently depend on the ground being saturated (framing +
    scratch not yet coherent/eager, `tr` still imports). They are the concrete
    S1 targets: the scratch path must be made equivalent (eager coherent scratch +
    scratch-side framing + `tr` lookup) before the reroute is green. S1 is
    therefore an atomic unit (reroute + framing-on-scratch + tr-lookup land
    together), best developed behind a `SILVER_OXIDE_TWO_EGRAPH` flag then flipped.
- **S2 — dual heap (invariant 7).** Thread a scratch heap; prove consume on it;
  record the guarded syntactic debit on the ground heap. Gate: aliasing corpus
  (`pred_merge`, `deref`) green; no perm regression.
- **S3 — invariants 5–6 hardening.** Restrict tier-3 to side-conditions; assert
  statement-level insts carry only block PC; delete now-dead ground-proving code.
- **S4 — cleanup.** Remove residual `block_scratch_*` overhead that no longer
  earns its keep; consolidate the two-mapping abstraction; update this tree + memory.

## Scratch heap inherits the block PC (identity semantics)

The scratch heap does **not** assume the PC per-location; it inherits it from the
scratch **egraph** (block cube assumed + saturated). Consequences:

- **Scratch heap chunk identity = scratch e-class equality on addresses** → PC-aware.
  A PC-implied alias (`x==y` under the branch) makes `x.f`/`y.f` the same class ⇒
  the same location; `find_chunk_consolidated` sums their perms (`1/2 + 1/2 = 1/1`).
  Resolved **lazily** on lookup/consume, not eagerly unioned at block entry.
- **Ground heap chunk identity = ground e-class** → PC-*unaware* (ground never
  assumes the PC unguarded). `x.f`/`y.f` stay syntactically distinct; a consume that
  succeeded on the scratch is recorded on ground as a **guarded debit** (the
  `-1/2` under this PC), never a consolidation.
- Only guarded propositions cross to ground; scratch-*derived* aliasing stays in
  the scratch and is discarded. (README invariant 1 — export discipline.)

Because the two heaps use **different identity semantics**, they are **two
separate `Heap` instances** (ground, scratch), not one heap with dual-id chunks.

## Decisions

- **Framing (Q1): scratch-side in S1.** Ground stays strictly raw from day one —
  no in-block ground `reduce`/`saturate`. Snapshot-tower normalization and slot-
  address e-class matching resolve in the **scratch**. This pulls scratch-side
  address resolution into S1 (a slice of the heap work), keeping invariant 3 whole.
- **Heap representation (Q2): two `Heap` instances** (ground + scratch), per the
  identity-semantics argument above.

## Block-PC redundancy (clarification, 2026-07-29)

Today the block cube is stored/applied redundantly, which invariants 4/6 clean up:

- **Lowering** (`method.rs:516`) wraps the whole block body in
  `with_conds_kind(&pc, Cube, …)`, so **every** in-block statement gets
  `inst.pc = block.cube` — the cube is stored twice (on `block.cube` *and* each
  statement's `inst.pc`).
- **Ground:** the cube is applied **once** — as the `inst.pc` guard on the
  inhale-assume / exhale-prove. This is **load-bearing** (invariant 4: ground
  facts must be guarded by the full PC so they don't leak to siblings) and equals
  the block cube exactly (invariant 6: no *extra* suffix).
- **Scratch:** applied **twice, redundantly** — assumed in the scratch *and*
  carried as the obligation/assume guard. Redundant (folds to a free hit), not
  unsound. Invariant 4 removes it: scratch assumes go in **unguarded** (the
  scratch already holds the cube); ground keeps its guard.

## Open decisions (resolve during S1/S2)

- **Guarded ground debit shape (invariant 7):** the exact ground-heap encoding of a
  consume that only succeeds under PC-implied aliasing (a guarded negative-perm
  chunk vs. a guarded consume record). Ties to `project_block_heap_consume_model`;
  settle when S2 lands the divergence, with the adversarial `x.f/y.f` test.

## Verification

- Repro fixed: `verify …/generic_option__match_flat.vpr` completes, no panic.
- Feature matrix 27/27 run without panic; none regress pass→fail.
- `cargo test --lib` 303/303, `tests/suite.rs` 3/3, `tests/perf_regression.rs` 1/1.
- Invariant probes: assert `tr` never misses; assert statement-level insts carry
  block-only pc; an adversarial aliasing test for invariant 7 (the `x.f/y.f`
  union-then-exhale case) verifies with the guarded ground debit.
- Perf: `gen_enum_match` N=16/24/32 + `structs_enums_base` neutral-or-better vs
  HEAD (ground no longer saturated/reduced in-block is a net reduction in work).
