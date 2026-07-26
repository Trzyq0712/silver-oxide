# 80 — Implementation plan (v1: single ground e-graph)

**Branch:** `backend-blocks` (off `backend`). Cross-check every stage against `backend`.

**Scope of v1 (locked):** ONE shared ground e-graph, exactly as today. **No** per-block
local, **no** ghost archive, **no** fork/merge, **no** enode-id remap. This sidesteps the
two hardest seams (graph merging + enode-id persistence) entirely. The tier-4 killer does
**not** need them: the exit-perm collapse is a *structural* merge over **explicit perm
terms** + a binary-join `ite`-collapse (`[30]`/`[50]`), which runs fine on one graph.

Consequence for the milestone map (`70`): the correctness win lands on the path
**M1 (block IR) → M3 (structural joins)**, **skipping M2 (local/ghost split)**. M2 —
forking, isolation, remap, live-cone — is deferred to a later v2 and is **not** on this
plan's critical path. Everything below is v1 unless tagged `[v2-deferred]`.

Grounding facts (measured `backend`, 2026-07-25, don't re-derive): every mut-through-match
/ owned-return case = **exactly 1 tier-4 split** (the exit `exhale …#ensures 1/1`); the
value phi already collapses (`build_entry_env`, `reach.rs:193`); the perm does not — it
accumulates as `Σ ite(flag,1/1,0)` with a `0` fall-through. VMIR is no longer quadratic
(`1b53e98`). See `README.md` "Ground-truth facts."

---

## Where the code seam is (verified 2026-07-26)

The block structure **already exists at translate time and is thrown away**:

- `translate/decl/method.rs` (`lower_method:221`) walks the Viper CFG in **topo order**
  (`cfg.topo_order():287`), computes each block's reach DNF + pc + `reach_val`
  (`block_reach`), phi-merges variable environments at joins (`build_entry_env`,
  `reach.rs:193` — exhaustive-edge `ite`, last arm unguarded), and threads a **single
  linear heap** `current_heap` (`:268`, comment `:229` "the heap is *not* phi'd") across
  blocks. It then **flattens** everything into `Method.insts: Vec<Inst>` (`vmir/method.rs`).
- `verify/declaration.rs` (`verify_method:2433`) runs `walk_body` (`:2422` loop) over that
  flat `&[Inst]`, one `EvalState`, one e-graph.

So block-VMIR v1 = **stop flattening** (keep the blocks the linearizer already has) + **walk
blocks** join-then-body in topo order + (at Stage 4) **route the heap through a per-join
`Merge`** instead of the single linear timeline. The reach/phi machinery is reused verbatim.

**The single change that kills tier-4** (Stage 4): today `current_heap` is threaded so a
join-block's heap is whatever the *previous topo block* left — the perm partition
accumulates additively. Block-VMIR derives a join-block's `h_in` from its **CFG preds** via
a structural `Merge` that SELECTs arm perms under exhaustive edges (`[30]`) → the `0` leaf
never forms → `1/1` structurally.

---

## Stage 0 — Scaffolding & A/B harness (no IR change yet)

**Goal:** be able to run block-path and linear-path side by side and diff, before any block
code exists. De-risks every later gate.

1. `SILVER_OXIDE_BLOCK` env flag (precedent: `NO_TIER4` at `context.rs:528`). Off ⇒ today's
   linear path byte-for-byte. On ⇒ block path (stubs until Stage 1).
2. **A/B diff harness**: a script that runs `structs_enums.vpr` + corpus + `gen_enum_match.py
   {8,18,20}` under both flag states and diffs (pass/fail per method, tier-4 count via
   `SILVER_OXIDE_TRACE_SIZE`, node/class counts). This is the M1 no-op oracle.
3. **Freeze the baseline**: capture `backend`'s current results table (305/305, tier-4
   counts, base timing on `structs_enums.vpr`) into `design/block-vmir/baseline.csv`.

**Gate:** harness runs, both columns identical (flag is a no-op stub). Baseline captured.

**Touch:** `verify/context.rs` (flag plumbing), a `scripts/ab_diff.py`, `baseline.csv`.

---

## Stage 1 — Block-VMIR IR types (`[10]`)

**Goal:** land the block graph as a *type*, with `Display`, no lowering/verify use yet.

Per `[10]` Rust mapping — reuse the whole `Val/HeapVal/Perm/Inst/PureInst/HeapInst/PathConds`
vocabulary; add only the CFG layer:

```rust
// vmir/method.rs
pub struct Method {
    pub name:   Spur,
    pub blocks: TiVec<BlockId, Block>,   // TiVec already used in vmir/mod.rs
    pub entry:  BlockId,
    // KEEP `insts: Vec<Inst>` too, for now — see migration note below.
}
pub struct BlockId(usize);              // derive From/Into, TiVec index

pub struct Block {
    pub cube:  PathConds,               // CONTROL cube (was per-inst pc, from block_reach)
    pub preds: Preds,
    pub join:  Vec<Inst>,               // phi `Ternary`s + (Stage 4) the heap `Merge`
    pub body:  Vec<Inst>,               // straight-line SSA
    pub h_out: HeapVal,                 // cached last heap produced (else h_in)
}
pub enum Preds {
    Entry,
    From(BlockId),
    Join { cond: Val, then_: BlockId, els: BlockId },
}
```

One new inst variant, **stubbed** (unreachable until Stage 4):
```rust
// vmir/inst.rs HeapInst::
Merge { cond: Val, then_h: HeapVal, els_h: HeapVal }
```

**Migration note — keep `Method.insts` alongside `blocks` through M1.** Do NOT delete the
flat vec in Stage 1. The verifier still reads `insts`; adding `blocks` next to it lets
Stage 2 populate blocks and Stage 3 switch the reader, each independently green. Remove
`insts` only after Stage 3's gate passes.

**Deliverables:** types compile; `VmirDisplay` for `Block`/`Method` (join/body sections,
`<cube>` header, `from bbP` / `join eC [bbA,bbB]` pred line — the `[10]` syntax); a
round-trippable debug dump behind a flag.

**Gate:** `cargo build`; `cargo test --lib` green (nothing consumes `blocks` yet).

**Touch:** `vmir/method.rs`, `vmir/inst.rs`, `vmir/display.rs`, `vmir/mod.rs`.

---

## Stage 2 — Block lowering (populate `blocks`, keep flattening)

**Goal:** `lower_method` fills `Method.blocks` **in addition to** `Method.insts`. The two
must be equivalent: the flat `insts` = the blocks concatenated join-then-body in topo order.

- The linearizer already has everything: `order` (topo), `reach_pc[bid]` → `Block.cube`,
  `build_entry_env` output → the join-phase `Ternary` phis, per-block lowered `Inst`s →
  `Block.body`. `Preds` reads off `cfg.predecessors()` + `Terminator` (`Goto`→`From`,
  `If`→`Join{cond,then,els}` on the successor side; entry→`Entry`).
- **Heap in Stage 2 stays the single linear timeline.** `Block.h_out` = `current_heap`
  after the block; the join phase emits **no `Merge` yet** (Merge lands Stage 4). `h_in` is
  still "previous topo block's `h_out`." This is deliberate: Stage 2+3 are the **no-op
  refactor**; the heap semantics must not change until Stage 4.
- `join` vs `body` split: the `build_entry_env` phis + `label`-capture go in `join`; the
  `lower_stmt` output goes in `body`. The per-inst `pc` narrows to the **expression pc**
  (`Branch`/`Fact`, `sink.rs` `PcKind`); the **control** part moves to `Block.cube`
  (`[10]` §pc). For Stage 2, simplest correct move: leave each inst's `pc` as-is and set
  `Block.cube` = `reach_pc[bid]`; the walker (Stage 3) uses `cube` for block-level gating
  and keeps honoring inst `pc` unchanged → identical obligations. The pc *split* (stripping
  the control prefix off inst pc) is a **Stage 5 cleanup**, not needed for the no-op.

**Deliverables:** `blocks` populated; an assertion (debug-only) that flatten(`blocks`) ==
`insts` for every method in the corpus.

**Gate:** the flatten-equality assertion holds across corpus + `gen_enum_match`; `insts`
still drives verification unchanged ⇒ 305/305, tier-4 counts unchanged.

**Touch:** `translate/decl/method.rs`, `translate/reach.rs` (expose phi list separately),
`translate/sink.rs` (optional PcKind read).

---

## Stage 3 — Block-topo walker (switch the reader) — completes **M1**

**Goal:** under `SILVER_OXIDE_BLOCK`, the verifier walks `Method.blocks` (join then body,
topo order) instead of `Method.insts`, over the **same single e-graph / single EvalState**.

- New `verify_method_blocks` beside `verify_method`: iterate `blocks` in topo order (derive
  from `Preds`, or reuse a stored `entry` + successor inversion). For each block: run `join`
  insts, then `body` insts, through the **existing** `eval` / `walk_body` inner loop (reuse
  it — pass a block's inst slice). One `EvalState`, one heap threaded in **topo order** (as
  Stage 2 — no Merge yet).
- Block-level pc gating: the block `cube` is assumed by pc-gating its insts exactly as the
  flat path did (the inst pcs are unchanged in Stage 2, so this is literally the same
  evaluation, just re-grouped). **This is why M1 is a no-op.**
- Snapshotter/stats: keep working (block headers in the trace are a bonus).

**Deliverables:** block walker; `SILVER_OXIDE_BLOCK=1` runs the full suite.

**Gate (the M1 gate — the key early de-risk):** `ab_diff.py` shows **byte-for-byte
identical** results block-path vs linear-path: 305/305, **same tier-4 count**, same
node/class counts. If anything moves, the block grouping is wrong. After this passes,
**delete `Method.insts`** and make the block path the only path (retire the flag's off
branch, or keep it as `BLOCK=0` → error for one release).

**Touch:** `verify/declaration.rs` (`verify_method_blocks`, reuse `walk_body` inner loop).

---

## Stage 4 — Structural perm/heap `Merge` at joins — the tier-4 killer (**M3**)

**Goal:** derive a join-block's `h_in` from its **CFG preds** via a structural `Merge` that
SELECTs arm perms under exhaustive edges → exit perm collapses to `1/1` with **no split**.
This is the whole point. `NO_TIER4` must go green on the enum family.

Four pieces, in dependency order:

**4a. Explicit perm term + smart constructors (`[50]`).** Perm is already `vmir::Perm =
Amount(Val) | Wildcard | Ite(Val, Box<Perm>, Box<Perm>)` — the "explicit term outside the
e-graph" *exists*. Add **smart constructors** that canonicalize at construction (no
saturation, no budgets): `const-fold`, `ite(c,x,x)→x`, `(x−q)+q→x`, **identity-else
collapse** (`ite(P, old±amt, old)` with zero net delta → bare `old`). Store perms as
**identity-else reach-guarded deltas** so an amount-preserving op leaves the inherited
amount **bare** (`[30]` "read-off, not extract-then-rewrite"). Verify the give-back nets to
a bare `Const` by structural walk, leaves compared via e-class `find()`.

**4b. Heap `Merge` eval + `h_in`-from-`Preds`.** In the block walker, a `Join`-pred block's
`h_in` = `merge(then_.h_out, els_.h_out) on cond`, a **per-chunk structural merge**
(`[30]`): for each location, SELECT the arms' explicit perm terms under exhaustive edges —
`ite(e0,p0,ite(e1,p1,…p_last))`, last unguarded, **never additive Σ**. The merge runs **in
the join block's context** (its `cube` = common prefix `X` assumed) so the full-cube guard
`X&&d` folds to the edge `d` and the select collapses (`[30]` guard-granularity result).
Closed pattern set (`[40]` table): same-amount→collapse `p`; inherited-untouched→collapse;
reachable+dead-sibling→`ite(X,p,0)` (Route 1); divergent→keep `ite(edge,p,0)`; different
live amounts→keep `ite(edge,p,r)`. **Structural dispatch, not rewrite rules.**

**4c. Dead-block skip (Route 1).** A block whose `cube` the walker proves inconsistent
(`bb_unreach`, same-value nested `unreachable!()` = const-fold contradiction) is
`Inconsistent` → its arm folds out of the `Merge`/phi `ite` at **verification time** (topo
order guarantees preds processed before the join). `reach` stays deadness-agnostic.

**4d. Value phi through the same Merge path.** Values already collapse (`build_entry_env`);
confirm the join now reads them consistently with the heap merge (unified dispatch, split
medium — `[30]` value-merge table). On one shared e-graph, "id stability" is trivial (no
remap — global positional temps, as today), so the `[20]` fork/remap machinery is **not
needed** here.

**Deliverables:** `Merge` eval; smart-constructor perm module; dead-block skip; the
`[30]`/`[50]` worked enum trace reproduced as a test.

**Gate (the M3 gate):** `SILVER_OXIDE_NO_TIER4=1` **green on the enum family**
(`enum_clike__mut_through_match`, `gen_enum_match {8,18,20}`); the exit-perm goal collapses
with `prove_splits: 0`; `gen_enum_match {20,100}` verify with **no arm-count cliff**; full
suite + corpus still green **with tier-4 still enabled** (Merge must not regress anything).

**Adversarial canaries to add here:** `divergent.vpr` (footprint divergence, risk 6 — may
still need Z3/tier-4, that's acceptable and expected); nested-binary enum dead-arm (Route 1);
same-value nested `unreachable!()`.

**Touch:** `verify/heap.rs` + `verify/declaration.rs` (`Merge` eval, `merge_chunks`
neighbour), new `vmir/perm.rs` or `verify/perm.rs` (smart constructors), block walker
(`h_in` from `Preds`).

---

## Stage 5 — Rule diet + pc cleanup (**M4**)

**Goal:** remove linearization-era machinery the structural join makes dead, one at a time,
ablation-gated. Also do the deferred pc split.

- **pc split** (deferred from Stage 2): strip the control prefix off each inst's `pc`,
  leaving only the expression pc (`Branch`/`Fact`); the block `cube` carries control. Pure
  cleanup; gate = no result change.
- **`merge_ite_sum` / `flatten_plus` / `merge_summands`** (`context.rs:837/845/885`): the
  additive partition-collapse plumbing. Block joins SELECT, never sum → these should be
  **dead**. Confirm by ablation, then delete (don't port). `[40]`/`[50]`.
- **`lt-ite`** (`rewrite.rs:481`): its job is `perm ≥ 0` on scaled `c?p:0` perms. Inside a
  block, inhaled perm is literal `p` → `p ≥ 0` const-folds → lt-ite's reason evaporates
  (`[40]` thesis). Demote to bounded reductive descent (for phi-selected conditional perm)
  or delete. **Measure on block-based** — `NO_LTITE + NO_TIER4` on the enum family. Keep a
  canary; the flat `gen_8` generator needed it, real Prusti mut did not.
- **`eq-ite`**: likely removable earlier; ablate.
- **tier-4** (`split_prove`/`split_tree`/`SPLIT_BUDGET`): once Stage 4's gate holds, remove;
  keep tier-3.5 non-forking descent (`f55f6c0`) + a Z3 escape hatch **only** for
  footprint-divergence residue (`[30]`/`z3_integration_plan.md`) if/when Z3 lands.

**Gate:** each removal keeps suite+corpus green, `NO_TIER4`-independent, and does **not**
regress base timing. Record verdicts in `40-rewrite-rules.md`'s rule→tier table. Re-run all
ablations at the end and diff against `[40]`'s current numbers.

**Touch:** `verify/rewrite.rs`, `verify/context.rs`, `verify/declaration.rs`.

---

## Stage 6 — Harden (subset of **M5**)

v1-relevant hardening only (loops + local/ghost-specific risks are v2):

- **Canaries from `[60]`**: footprint-divergence (risk 6), same-fact-both-arms telescoping
  (risk 5), infeasible-cube block exports nothing spurious (risk 2). On one graph the
  pc-leak canary (risk 1) is moot until v2 (no local↔ghost boundary yet) — note it as
  v2-gated.
- **Quantifier branch-pollution (`project_quantifier_branch_pollution`)**: on one shared
  graph this accepted unsoundness is **not** fixed by v1 (the structural fix needs per-block
  locals = v2). Document that v1 leaves it as-is; do not claim the fix.
- **Real Prusti validation (risk 10)**: validate the collapse on a real Prusti dump
  (`tools/prusti_encode.sh`), not only `gen_enum_match`. Highest value: a Prusti-generated
  nested-`&mut` case (`[30]` risk).
- Cleanup: remove the A/B flag scaffolding once block path is sole path.

---

## `[v2-deferred]` — not on this plan's critical path

Explicitly **out of v1** (single-graph constraint). Pick up only if measurement demands:

- **M2 proper**: per-block local + ghost archive, propositions-only export, live-cone
  seeding (`[20]`). The correctness win does **not** need it.
- **Ghost fork / merge / enode-id remap** (`[20]`) — the value e-node *scaling* story. The
  seam the user asked to avoid; avoided by construction here (global positional temps).
- **Loops / back-edges** (`[60]` risk 7): DAG-only for v1. `Block`/`Preds` type must not
  preclude a graph (it doesn't — `Preds` allows a later-topo pred); invariants + havoc
  later.
- **Quantifier branch-pollution structural fix** (needs locals).
- **Z3 tier** for footprint-divergence residue (`z3_integration_plan.md`).

---

## Stage → design-doc → milestone map

| Stage | does | design docs | milestone | gate |
|---|---|---|---|---|
| 0 | flag + A/B harness + baseline freeze | 70 | — | harness diffs, no-op stub |
| 1 | block IR types + Display | 10 | M1a | builds, `--lib` green |
| 2 | populate `blocks` (keep flatten) | 10, 30 | M1b | flatten==insts, 305/305 |
| 3 | block-topo walker (switch reader) | 10, 20(v1-subset) | **M1** | **byte-identical A/B** |
| 4 | structural `Merge` + explicit perm + dead-skip | 30, 50, 40 | **M3** | **NO_TIER4 green on enum, no N-cliff** |
| 5 | rule diet + pc split | 40 | M4 | each removal green, no time regress |
| 6 | canaries + Prusti validation | 60 | M5-subset | canaries pass |

**Note the skipped M2:** v1 goes M1→M3 directly. M2 (local/ghost/fork/remap) is v2.

## Invariants to protect at every stage (from `README.md`)

1. Exports carry propositions, not e-graph state. *(v1: no local↔ghost boundary, so this
   binds only when v2 lands — but Stage 4's `Merge` must build the collapsed perm from
   **as-written/inherited** amounts, never from a value proven-then-extracted under pc.)*
2. Joins built exhaustive-edge (last arm unguarded), perm **and** value. No manufactured
   `0`/fall-through leaf at a real CFG join. **This is the structural collapse; never a
   proof.** (Stage 4 core.)
3. Trigger matching depends on congruence, never reductive normal form.

## First concrete step

Stage 0: add `SILVER_OXIDE_BLOCK` plumbing + `scripts/ab_diff.py` + freeze `baseline.csv`
from current `backend`. Then Stage 1 IR types. Land each stage as its own commit on
`backend-blocks`; cross-check against `backend` via `ab_diff.py` at every gate.
