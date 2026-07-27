# Block-VMIR — progress log

Running, between-sessions record of the block-structured VMIR effort (branch
`backend-blocks`). Newest entry on top. Design in this tree (`README.md`, components 10–70);
staged build plan in `80-implementation-plan.md`. One entry per work session — what landed,
key decisions, test state, what's next.

Milestone shorthand (from `80`): **M1** block IR + block walker (no-op refactor) → **M3**
structural joins (tier-4 killer) → **M4** rule diet. v1 = single ground e-graph, no
local/ghost fork/remap.

---

## 2026-07-27 (later) — structural ChunkPerm: kill Select materialization (256s→4.6s)

`structs_enums.vpr` under the flag was **256s** (vs 2.5s OFF), egraph 9× bigger, 1.19M rule
applications. Two causes, both fixed:
1. `ChunkPerm::to_id` lowered join `Select` perm-trees into the ground graph → the `ite`
   dragged snapshot-fn unfolds + forall + ite-reduce + `lt-ite` through every saturation.
2. `fold_under_pc` cloned the whole graph **per join** to fold a dead edge — dominant cost on
   struct CFGs (hundreds of joins). Found via the fast repro
   `feature_matrix.../enum_struct_variant__mut_through_match.vpr` (hung ON; graph was only ~2k
   nodes, so it was clone/saturate cost, not bloat).

Fix = **Select never materializes**. Perm predicates prove **per leaf** over the ChunkPerm
tree (`prove_perm_leaves`: recurse Select, push cond → pc, discharge each Leaf under the
accumulated pc). Dead inner edge auto-discharges: its arm's pc = `block_cube ∧ ¬edge`,
contradictory when cube⇒edge → leaf vacuous, no clone. New `prove_sufficient` /
`prove_perm_positive` / `prove_perm_write` / `perm_sub` (structural remainder) /
`perm_all_zero`. Converted heap_subtract, assume_location_axioms (bound per-leaf, non-alias
Leaf-only), Assign, Presence, Deref-framing off `to_id`. `fold_under_pc` reduced to a live
`known()` check (no clone). Dropped per-join `ctx.reduce()`.

**Result:** structs_enums ON **256s→4.57s**, nodes 38320→7296, rule_applications 1.19M→9.9k,
`prove_tier4` 6→0, `prove_splits` 0, 0 fails. Small struct cases now faster ON than OFF. Flag
OFF byte-identical (303 lib + suite). Watch: `prove_calls` 227k vs 4.9k OFF — per-leaf proving
does many cheap tier-1 proves (headroom, not critical). Commits `e0e59ba` + cleanup.

---

## 2026-07-27 — Stage 4.0–4.3 landed: structural heap merge kills enum tier-4

All behind `SILVER_OXIDE_BLOCK_MERGE` (default OFF). Flag OFF stays byte-identical to
Stage 3 (303 lib + full suite green). Commits: `7c6f1b6` (4.0/4.1), `c54add9` (4.2/4.3),
`1422570` (fork-correctness fixes).

**Landed:**
- **4.0/4.1** `ChunkPerm` (`Leaf(Id) | Select{cond,then,els}`) held outside the union-find;
  smart ctors `select`/`same`/`to_id`; `Chunk.perm: ChunkPerm`. Migrated
  merge_chunks/heap_union/heap_subtract/find_chunk_consolidated/location_chunks/Deref/Assign
  to read perms via `to_id`. Aliasing perms stay `Leaf`. `Leaf`+`to_id`-identity ⇒ flag-OFF
  byte-identical.
- **4.2** lowering: per-block `h_in` from `Preds` (`HeapInst::Merge` at a `Join`, carrying
  the block cube as its pc), `h_out_of` map, synthetic n-ary joins emit `Merge` too. Verify
  `merge_heaps`: per-kind/per-canonical-addr structural SELECT; give-back arms both fold to
  `1/1` ⇒ `same()` collapse. `Heap::kinds`/`chunk_canon`.
- **4.3** dead-arm dropping: (a) `fold_under_pc` scratch-clone probe assumes the join cube to
  fold a dead edge; (b) `EvalState.dead_heaps` tags an unreachable block's exit heap (cube
  refuted in the ground graph, e.g. `bb_unreach` after `inhale false`) so the merge drops
  that arm instead of a `0`-leaf.

**Architecture confirmed (the key realization):** GROUND e-graph = **storage** — never
assumes a block cube (a global cube-assume makes sibling branches inconsistent → unsound;
verified by a throwaway `ASSUME_CUBE` diagnostic that both collapsed the tower *and*
demonstrated the poisoning). SCRATCH clone = **decision** — `fold_under_pc` assumes the join
cube transiently to fold dead edges, then discards (same clone-and-throw as tier-3/4). This
is the minimal slice of the "ghost + local egraphs" direction.

**Fork-correctness fixes (`1422570`):** the assume-in-resources design had put the branch in
the *perm scale* (`gate_perm`), not `inst.pc`. Removing scale-gating under the fork model
leaked. Fixes: new `PcKind::Cube` (rides in `pc`, excluded from `branch_conds` so
gate_perm/gate_value keep gating genuine spatial `b ? A : A'` conds but not the cube); the
`inhale` is emitted **guarded** under the flag and its produced bool is guarded by the block
cube. Reverted the blanket gate no-ops.

**Result:** `gen_enum_match {2,3,8,20}` verify with `NO_TIER4=1` — `prove_splits: 0`,
`prove_tier4: 0`. Whole `tests/cases/passing/permissions` corpus verifies flag-ON + NO_TIER4.
Passing corpus no regressions; every failing corpus case still fails flag-ON (soundness).

**Deviation from `81`:** the plan put the enum gate at 4.2 and unreachable-block handling at
4.3, but the failing split is the exhaustiveness `0`-leaf (the `bb_unreach` arm), so 4.2's
gate actually needs 4.3's dead-arm mechanism — landed together. The plan's "walker assumes the
block pc" premise was false; replaced by the ground-storage / scratch-decision split above.

**Next (4.4, a deliberate decision — NOT done):** flip `SILVER_OXIDE_BLOCK_MERGE` default ON.
Blocked on: (1) flip the `both_arms_..._case_split_we_lack` e2e assertion — the fork join now
*proves* it (its comment anticipates this); (2) run the full 305-case `structs_enums` corpus
flag-ON (not in-repo); (3) refresh `benchmarks/baseline/*` + review the cost diff (should
drop — tier-4 gone). Then prune the now-dead `gate_perm`/`gate_value`/linear-thread paths.

---

## 2026-07-27 — Stage 4 plan written (pre-implementation)

**Status:** design only, no code. Wrote the code-level Stage 4 guide
`81-stage4-implementation.md` (indexed in README) for the implementing agent: concrete
types, signatures, pseudocode, line anchors into the current tree.

**The three deliverables (user-requested):**
1. **Heap storage** — `Chunk.perm: egg::Id → ChunkPerm { Leaf(id) | Select{cond,then,els} }`.
   `Leaf` = anything the frontend built, INCLUDING a program-written `c ==> acc` gated ite
   (opaque, never decomposed — "nothing we can do, throw into the e-graph"). `Select` is
   built ONLY by the join merge (control flow) = the explicit structure. Smart ctors:
   same-amount collapse (`then≡els⇒then`, give-back), dead-arm drop under block-cube fold,
   const-fold; `to_id` lowers to an e-graph `Ite` only where the prover needs an e-class.
   Merge consults **block PCs only**.
2. **Smart joins** — `merge_heaps(cond, h_then, h_els)` per chunk: both-hold ⇒
   `select(cond, pt, pe)` (equal ⇒ bare constant = the tier-4 kill); one-side ⇒
   `select(cond, p, 0)` = divergent U4. SELECT across arms, ADD only within an arm. Nested
   joins collapse bottom-up via topo order. `HeapInst::Merge` arm calls it; lowering derives
   `h_in` from `Preds` and **drops `gate_perm`/`gate_value`** (arms run unguarded).
3. **Unreachable blocks** — detection == join-elimination == one const-fold, **no dead-block
   flag in v1**: a dead arm's edge `cond` folds false ⇒ `select` drops it ⇒ its `h_out` never
   selected. v1 detection = const-fold only (no assume — the single ground graph would be
   poisoned; no clone); body-skip is an optional perf layer; scratch-clone is escalation
   (not needed for the enum family). Route-1: divergent-but-dead side ⇒ no `0` leaf.

**Staging:** 4.0 flag `SILVER_OXIDE_BLOCK_MERGE` (default OFF, A/B) → 4.1 `ChunkPerm`
(gate: flag-OFF byte-identical) → 4.2 fork + `Merge` + drop gating (gate: `gen_enum_match 8`
`NO_TIER4` green) → 4.3 dead-arm → 4.4 scale N=100 + flip default. Plan mirror in
`~/.claude/plans/block-vmir-stage4.md`.

**Next:** implement 4.0/4.1 (await go).

---

## 2026-07-27 — Stage 3: block walker (verifier reconnected)

**Status:** landed, uncommitted on `backend-blocks`. Milestone: **M1 complete** (block IR +
walker, no-op refactor). Verified no-op vs `backend`.

**Shipped:**
- `verify_method` (`verify/declaration.rs`) is now a **block walker**: iterates
  `method.blocks` in stored order, running each block's `join` then `body` phase through the
  existing per-inst engine `walk_body` over one shared `EvalState`/e-graph. Heap threads
  **linearly** via each inst's explicit `base: HeapVal` (no `Merge`, no per-pred derivation).
  A marked **Stage-4 heap hook** sits at the per-block boundary; a `debug_assert` pins the
  stored-order-is-topological invariant.
- All 165 method-verify `#[ignore]`s removed; the full-program driver (`verify/mod.rs`) and
  corpus/perf tests reconnect unchanged.

**Load-bearing invariant (documented in code):** `EvalState` is positional
(`vals[n] == Temp(n)`), so the walker **must** evaluate in stored block order = emission
order = `flatten()` order. That is what makes it a faithful no-op.

**Verified no-op vs `backend`:**
- `cargo test`: lib **303 pass / 0 fail / 1 ignored**; `perf_regression` **baseline holds**
  (cost unchanged); `suite.rs` corpus **3/3** (passing/failing/known-limitations all correct).
- Tier-4 unchanged on the enum family (`gen_enum_match 8`): tier-4 ON → all `[OK]`
  (`prove_tier4:1, prove_splits:1`); `NO_TIER4` → `[FAIL] m_add: insufficient permission`
  (`prove_splits:0`) — the exit exhale still needs exactly its 1 split. **Zero new proving
  power**, as intended.

**Next:** Stage 4 — the tier-4 killer. Replace the linear heap thread with `Preds`-derived
`h_in` via `HeapInst::Merge`: per-location SELECT over explicit `Perm` terms + smart
constructors + dead-arm Route 1. Gate: `NO_TIER4` green on the enum family. Hook = the marked
per-block boundary in `verify_method`. (This is where the heap-tracking design work lands.)

---

## 2026-07-27 — Part 1: block IR + lowering (verifier disconnected)

**Status:** landed, uncommitted on `backend-blocks`. Milestone: first half of **M1** (the IR
+ lowering; the block walker is the second half, next session). `cargo test` green —
**143 lib pass / 0 fail / 161 ignored**, suite 3 ignored, perf 1 ignored.

**Shipped:**
- IR (`vmir`): `Method { blocks: TiVec<BlockId, Block>, entry }`; `Block { cube, preds,
  join, body, h_out }`; `Preds::{Entry, From, Join{cond,then_,els}}`. `HeapInst::Merge`
  declared as a **stub** (never emitted — heap still threads linearly). `Method::flatten()`
  / `iter_insts()` reconstruct the flat stream.
- Lowering (`translate/decl/method.rs`): reworked to emit blocks via `Sink::take_since`
  draining each phase into `join` / `body`; temps stay global-positional (no remap).
  `build_entry_env` → `merge_two_envs` (pairwise two-env phi).
- **Binary joins**; n-ary (>2-pred, multi-goto-label only) **normalized to a synthetic
  binary-join chain** (branch-tree order). Verified on a 4-pred merge (`ite(a,1,ite(b,2,
  ite(c,3,4)))`, two synthetic joins + real block).
- Block `Display` in the `10`-doc syntax.
- Verifier **hard-disconnected** for methods: `verify_method` → `Unimplemented` (fails
  loudly, no fake pass); `quant`/`context` route methods through `flatten()`;
  `analyze::method_deps` walks blocks. 165 method-verify tests `#[ignore]`d (both polarities,
  so no negative test passes spuriously).
- New tests: `diamond_lowers_to_a_single_binary_join`,
  `nary_merge_normalizes_to_a_binary_join_chain`, shared `assert_block_invariants`.

**Decisions this session:**
- **Binary joins, forced (branch-tree) order** — because the structural perm merger is
  inherently pairwise (dead-arm elimination + inner-before-outer collapse). N-ary from
  multi-goto labels is normalized, not gated. (`if/else`/`match` never produce >2-pred
  blocks — a k-way match is nested diamonds.)
- **Hard-disconnect** verify (over a flatten-bridge) — user's call; keeps the next stage
  building a real walker rather than a shim.

**Deviations from `80` (flagged):**
- Dropped the "byte-for-byte flatten == old stream" oracle (`build_entry_env` already used a
  `HashSet` for phi var order → old stream was itself run-nondeterministic). Replaced by
  structural-invariant tests.
- `Preds::Join.cond` = the then-edge reach value (= the phi guard, always available), not the
  bare branch literal via `merge_adjacent`. Bare-literal refinement is a later merger
  optimization; no effect this stage.

**Next:** Stage 3 block **walker** in the verifier — read `blocks`, walk `join` then `body`
in topo order over the single shared e-graph, linear heap; re-enable the ignored tests; gate
= byte-identical results vs `backend`. Then Stage 4 (`Merge` eval + explicit-perm smart
constructors + structural collapse + dead-arm Route 1) = the tier-4 killer.

---

## 2026-07-25/26 — design tree assembled (pre-implementation)

Multi-session design work (not code): `design/block-vmir/` filled in — component docs 10–70
(block IR, local/ghost verifier, joins/reachability, rewrite rules, heap residency, risk
register, migration gates) reconciled to neighbour-consistent, plus the staged v1 build plan
`80-implementation-plan.md` (M1→M3 skipping M2, single ground e-graph). Ground truth
(memory `project_exit_perm_representation_gap`): the sole remaining tier-4 split is the exit
`exhale …#ensures 1/1`, a **representation** gap — value phi already collapses, perm does not
(`Σ ite(flag,1/1,0)` with a `0` leaf). Block joins route perm through the same exhaustive
edge → structural collapse. VMIR no longer quadratic (`1b53e98`).
