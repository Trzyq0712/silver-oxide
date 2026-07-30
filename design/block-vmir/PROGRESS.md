# Block-VMIR — progress log

Running, between-sessions record of the block-structured VMIR effort (branch
`backend-blocks`). Newest entry on top. Design in this tree (`README.md`, components 10–70);
staged build plan in `80-implementation-plan.md`. One entry per work session — what landed,
key decisions, test state, what's next.

Milestone shorthand (from `80`): **M1** block IR + block walker (no-op refactor) → **M3**
structural joins (tier-4 killer) → **M4** rule diet. v1 = single ground e-graph, no
local/ghost fork/remap.

---

## 2026-07-28 — Stage 4.4 + Stage 5 landed: fork is the ONLY model; tier-4 slimmed to function-only

**Committed to the fork.** `SILVER_OXIDE_BLOCK_MERGE` flipped default ON, validated
(303 lib + 3 suite + perf baseline + feature-matrix all green, methods `prove_splits: 0`),
then the flag and the entire OFF (linear-thread) path were **deleted**. `block_merge_enabled`
gone; `method.rs` lowering emits `HeapInst::Merge`/`PcKind::Cube` unconditionally; the linear
`h_in` cursor + the `block_merge` conditionals in `sink.rs`/`declaration.rs` removed. Note:
`gate_perm`/`gate_value`/`PcKind::Branch` are **kept** — they are NOT OFF-path-only, they gate
function-body ternaries (`pure_exp.rs`) and predicate/footprint conditions (`spatial.rs`).

**KEY FINDING — tier-4 is NOT fully replaced.** The fork restructures **method CFGs** into
blocks; **pure functions** stay expression trees. A branching function whose `?:` arms
establish `result` differently still needs a case split — even `absv(x){x>=0?x:-x} ensures
result>=0` fails without one (confirmed identical on committed HEAD, so this is pre-existing,
not a regression; `absv` itself also needs sign arithmetic the e-graph lacks — `clamp` and the
two `*_post_under_a_branch_via_case_split` e2e tests are the real guards). So tier-4 was
**slimmed, not deleted** (user decision): the heavy method-oriented machinery
(`split_tree` iterative-deepening, `SPLIT_BUDGET`, whole-pc-cone `split_candidates`) is gone,
replaced by a **goal-directed, function-only** `split_prove`/`split_goal` — reads candidate
conditions off the **goal term only**, depth-first, terminated by an `assumed` set, no budget.
Behaviorally identical to old tier-4 on function cases; methods never reach it (splits=0).

**Rule diet (Stage 5).** Removed: `lt-ite` (+ `LtBucketSearcher`/`LtIteDistributeApplier`/
`LtPlan`) — its job was the scaled-perm `c?p:0 ≥ 0` obligation, gone under per-leaf proving
(A/B: lib+suite+perf green without it, fires 0× on baselines); the `PRUNE_ITE` opt-in
`ite-then/else-context` pair — targeted a select tower the fork never materializes; the
commented mult/plus/minus/real-ite blocks; and the now-decided experiment env-knobs
(`NO_LTITE`/`NO_DISTRIB`/`NO_EQITE`/`NO_MIRROR`/`NO_CONTRA`, `NO_TIER4`). **Kept** (argued):
all algebraic give-back cancellation (`add-sub-cancel`/`sub-self`/… — cancel borrow cycles,
a mechanism SEPARATE from CFG-join towers), disequality unit-prop (`eq-false-*`,
`contra-congruence`, `eq-false-mirror`), `ite-reduce`, quantifier/function rules.

**`merge_ite_sum` DROPPED entirely** (user: "all perm reasoning should happen directly").
Both uses gone — the `prove_perm_ineq` lazy collapse AND the `merge_chunks` eager
additive-aliasing collapse — plus `flatten_plus`/`merge_summands`/`prove_merge_fallback`.
`prove_perm_ineq` and `prove_obligation` collapsed into plain `prove_under_pc`; with the
NoSplit gating gone the whole `Escalate` enum + `prove_under_pc_esc` were inlined away (every
prove now runs the full ladder). Structural per-leaf proving (`prove_perm_leaves`) covers what
the collapse did: 303 lib + 3 suite + perf all green (baselines unchanged — the collapse never
fired on them), method corpus fails=0/splits=0, aliasing corpus (pred_merge/deref) still green.
Net src delta for the whole session ≈ **−660 lines**.

**Gate:** external `structs_enums` corpus (user-run) is the final soundness check before merge.

---

## 2026-07-27 (end of session) — full tier-4-hunt clean; no perf regressions; Stage-5 scoped

**Feature-matrix tier-4 hunt (analysis/feature_matrix_2026-07-24/vpr, 27 cases): ALL verify
`NO_TIER4` with `prove_splits: 0` under fork** — including all 16 that were tier-4-load-bearing
(composite/enum_clike/enum_struct_variant mut-through-match, enum_tuple flat/return-owned,
generic_option/option_like/result_like matches, nested_struct__nested_if, nscale_04..20,
rec_list_len, rec_list_sum). Old backend still forces tier-4 on these (confirmed: they fail
OFF+NO_TIER4). Fork eliminates tier-4 across the ENTIRE corpus, not just the enum perm-cycle.

**Perf vs `backend` branch (233b205, real binary): fork strictly dominates, ZERO degradations.**
3-way (backend-t4 / this-branch-OFF-t4 / fork-ON): fork is ~2× on tier-4 cases (nscale_20
6.76→3.14s, composite 0.48→0.27, rec_list_sum 0.19→0.08), 0.95× on structs_enums, 1.0× on
trivial. Never slower. Block-VMIR refactor's OFF (tier-4) path ≈ backend ±10% jitter (neutral).

**Stage 5 (rule diet) — measured, LOW VALUE:** under fork `lt-ite` is removable (0 fails, its
flag-OFF job = scaled-perm `c?p:0` obligations, gone in fork's per-leaf proving) and tier-4 is
removable (splits=0) — BUT both give ~0 speedup (not the bottleneck). `NO_EQITE` gates
`eq-false-then/else` = **disequality unit-prop on `==` towers, NOT ite-distribution** (user
corrected me) — NEEDED both paths. **Real bottleneck = `ite-reduce` apply (5.7s of m_add's
9.3s @N=30)** collapsing the O(N) VALUE/snapshot ite towers (perm towers already killed). Rule
diet is a code-cleanup only (delete lt-ite/tier-4 after 4.4 flip), not perf. Real perf levers:
(1) incremental/dirty-set saturation (kills O(N)blocks×O(N)graph = the N² re-saturation),
(2) snapshot-fn opacity (we expand p_Case_snap, Silicon keeps opaque = O(N) graph growth),
(3) structural value-select like perms (harder — values read constantly).

**Silicon measured** (viperserver, see [[reference_silicon_scaling]] / [[reference_viperserver_measurement]]):
single-threaded ALSO superlinear (~N^1.7→N^3.75), NOT linear; fork faster to ~N=25-30 crossover.

**OPEN for next session:** (a) Stage 4.4 default flip — strong case now (full tier-4-hunt clean,
no regressions); needs: flip `both_arms_..._case_split_we_lack` e2e assertion, full corpus
flag-ON, refresh baselines. (b) heap_union/merge_chunks still `to_id`s a Select existing
(~decl:856) — additive aliasing, rarely bites. (c) Decide Stage-5 cleanup vs real-perf
(incremental saturation) direction. Repo `enum16.vpr` left for user's viperserver runs.

---

## 2026-07-27 (later still) — ite-idempotence flatten: structs_enums ON now BEATS OFF

After the structural-ChunkPerm fix, `structs_enums.vpr` ON was 4.3s (OFF 2.3s), dominated by
`m_shape_grow` (3.2s). Profiled: one location's perm was a **196,610-leaf Select tree**;
`same()` collapsed only 2262 of 225749 selects (1%); 222k per-leaf proofs. Root: the perm
accreted a `Select` layer at **every** join it survived (`m_shape_grow` = 361 blocks / 86
joins from Prusti overflow-checks + discriminant decode, NOT source nesting — only ~4 source
branches). Within one match arm, ~8 joins share the arm's reach cond, so the tree was nested
`Select(c, Select(c, …), …)` on the SAME `c`.

Fix (user's insight): `ChunkPerm::select` now flattens `ite(c, ite(c,a,b), e) = ite(c,a,e)`
(and the els dual) via `collapse_same_cond` — descend an arm while it re-branches on the same
condition class, keep only the decided branch. Keeps the tree linear in *distinct* conditions.

**structs_enums ON: 4.28s → 2.09s (faster than the 2.24s flag-OFF path!)**, prove_calls
225913 → 3308, nodes_peak 7295 → 4178, 0 fails, prove_splits 0 (OFF still needs 8 tier-4
splits). Flag OFF unaffected (Selects only built under BLOCK_MERGE). Commit `acd7074`.

**Net Stage-4 story: the fork model now matches/beats the tier-4 solution on the full struct
corpus AND is tier-4-free.** Remaining perf headroom minor.

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

---

## 2026-07-30 — S1: two-egraph id separation + `tr` crash fix (flag-gated)

**Status:** implemented, uncommitted on `backend-blocks`, behind
`SILVER_OXIDE_TWO_EGRAPH` (default **off**). Plans: `82-two-egraph-block-model.md`
(model/invariants) + `~/.claude/plans/plan-it-wise-taco.md` (S1 exec plan).

**Milestone met.** `analysis/feature_matrix_2026-07-24/vpr/generic_option__match_flat.vpr`
panics on HEAD (`egg unionfind index out of bounds`) and verifies 59/59 declarations
with the flag on. Gates: `cargo test --lib` 303/303 **both** polarities, `tests/suite.rs`
3/3 both, feature matrix 27/27 with 0 panics on.

**Shipped (on-path):** eager per-block scratch (`begin_block`); scratch assumes
**unguarded** (invariant 4, `scratch_assume_unguarded`); in-block `prove_under_pc`
routed to the scratch before the ground tier-2 `saturate`; ground `reduce()` disabled
in-block and run **between** blocks instead; framing matches in the scratch via
`heap_canons` (batched, one saturation per match) in `chunk_under_pc` +
`find_chunk_consolidated`; `reduce_scratch` cheap tier with `dirty`/`dirty_reduce`;
`prove_via_scratch` tiers reduce-then-saturate; `rewrite::Memo` overlays became a
**stack** keyed by scope id, and the block scratch `resume`s one scope for its whole
lifetime.

**Four id-mistranslation bugs (all silent; each broke a cluster of tests):**
1. `with_scratch_graph` swapped ground for a throwaway clone with the scratch still
   attached — the mirror recorded `map` keys that ceased to exist on restore.
2. `tr` began with `egraph.find(g)`. Ground canonicalization is not
   meaning-preserving for the scratch: once anything merges into the `true` class,
   ground `find` hands back the `true` leader, so every assumed fact translated to
   scratch-`true` and each mirrored union degenerated to `true == true`. Raw ids only.
3. Import used `egraph[g].nodes[0]` — an arbitrary member of the *canonical* class
   (`Lit(true)` for anything merged with `true`). Now `id_to_node(g)`, the node minted
   at that uncanonical id.
4. `watermark` used `total_size()` (`memo.len()`, which *shrinks* on a reduce), so
   pre-clone ids fell onto the import path and import rebuilt an **unmerged** copy of a
   class the clone already had merged. Now `egraph.nodes().len()`.

**Known deviation from invariant 1:** `tr` still imports (faithfully) instead of
asserting, because recipe `.build()` writes straight to `ctx.egraph`, bypassing the
`add`/`union` mirror hooks. Routing `build` through the mirror is the prerequisite for
the assert. Invariant 6's `unfolding`-rejection was not needed (no corpus case hits it).

**Perf: on is ~6× slower** — `structs_enums.vpr` 1.59s → 9.4s, corpus suite 0.43 →
2.67s. Measured causes:
- Ground *is* thinner (clone bases 39–1434 nodes; legacy ground peaked at 3861), and
  the prover graph is rebuilt per block from a cold applier memo.
- Sharing the memo across blocks (unsound experiment: scratch runs writing `base`)
  gives 9.47 → 4.88s, so ≈2× is **cross-block** re-derivation. The correct per-scratch
  overlay scope gave **zero** gain, which pins the loss as cross-block rather than
  cross-obligation — and memo bookkeeping cannot fix it, since block B's clone
  genuinely lacks block A's instances (suppressing the rebuild without the instance
  present would be a completeness bug).
- Remaining ≈3× unattributed: the scratch peaks at 32k nodes / 14.8k classes vs
  legacy's 3861 / 2867.

**Two things to keep straight when reasoning about that growth:** instantiation is
**presence**-triggered, not truth-triggered (`ForallApplier` adds the guarded
`Ite(forall, inst, true)` whatever the forall's truth; `f%pre` is a presence token) —
so guards were never keeping appliers dormant; the live hypothesis is trigger
*surfacing* (the assumed cube collapses `ite`s and merges classes, so more trigger
terms exist), still unverified. And unioning with `true` does not shrink the graph:
unions merge classes but never delete nodes.

**Failed experiments (recorded so they are not retried blind):** ground `saturate()`
at every block boundary (>2min); one ground `saturate()` per method (10.5s — ground is
near-empty at method entry); out-of-band export of conditional obligations
(23.3s — `record_proven`'s union into ground is load-bearing); scratch reuse across
same-cube chains (never fires, consecutive cubes always differ).

**Next:** the real lever is the ghost archive — let the *definitional* tier
(axiom/forall/function-unfold instances, unconditionally valid) land in ground so all
blocks share it, while PC-dependent derivations stay scratch-only. Then S2 (dual heap
+ guarded ground debit), S3 (tier-3/statement-PC hardening), S4 (cleanup + flip
default; perf-regression baselines need re-recording — the deltas are fingerprint-only).

### 2026-07-30 (same session) — pivot to a ground-first hybrid; crash fix is unconditional

Strict S1 (scratch = sole prover) cost ~6×, and a wall-clock breakdown by e-graph
(new `VerifyStats::graph_timing`) put **81% of the runtime in scratch
saturate/reduce** (7.64s of 9.4s), ground at 0.61s — *less* than the 1.08s ground
spends with the flag off — clone at 0.48s, probes at 0.02s. So neither the clone nor
the dual-graph bookkeeping was the problem; the cost was saturating a per-block graph.

**Ground-first (user's proposal, implemented).** Tiers 0/1/2 run on ground again and
the scratch becomes a *reusable* tier 3 — legacy behaviour plus reuse across
obligations that share a PC. If a block never needs the scratch it never pays for one.
Results: `structs_enums.vpr` **1.55s vs 1.59s off**, corpus suite 0.42 vs 0.43,
perm-cycle cases identical (0.16 / 0.11), scratch time 0.02s, lib 303/303 and suite
3/3 both polarities, feature matrix 27/27 with 0 panics, and the `perf_regression`
baseline passes again. Scratch counters on now match off exactly (14 clones / 14
saturations).

**The crash fix turned out to be unconditional.** `generic_option__match_flat.vpr`
verifies 59/59 with the flag **off** as well. The OOB was the four id-hygiene bugs —
above all the unfaithful `nodes[0]` import and the `memo.len()` watermark — not the
two-egraph discipline. Invariant 1 is therefore now "imports are faithful, so drift is
safe" rather than "drift is impossible by construction".

**Invariants 2 and 3 are no longer enforced**: ground is proven on and saturated
in-block. Soundness is unaffected (ground never has the PC assumed unguarded, so its
facts stay guarded and nothing leaks to a sibling or a join), but **S2 loses an
inherited argument**: the scratch heap's PC-aware chunk identity was justified by
ground never seeing PC-derived facts, and that justification has to be re-established
against the hybrid rather than assumed.

**Open question recorded separately:** assuming a PC *unguarded* inflates the graph
~8× (32k nodes / 14.8k classes vs 3861 / 2867) for the same obligation count, with 9×
the rule applications. Not applier-unblocking — instantiation is presence-triggered.
Leading hypothesis is trigger *surfacing* (the assumed cube collapses `ite`s and merges
classes, so more terms sit in matchable positions), unverified. This matters well
beyond the block work: it is the same shape as the heap-free-precondition pollution
multiplier, and it argues for keeping guarded representations and proving structurally
rather than by assumption.

### 2026-07-30 (same session) — adjusted S2 first increment: invariant 7 (pc-alias consume)

The S2 gate was an adversarial aliasing case, and it **failed on both polarities**
before this change: `requires acc(x.f,1/2) && acc(y.f,1/2)` then `exhale acc(x.f,1/1)`
under `if (x == y)`. Distinct chunks on ground; one location holding `1/1` wherever the
pc holds.

**Shipped** (`ctx.pc_alias_partners`, `ctx.gate_amount_by_pc`,
`heap_subtract_pc_aliased`): when the plain sufficiency proof fails, probe for chunks
that alias the demanded address *only* under the pc, prove `Σ holds ≥ needed` under the
pc, assume value agreement **guarded** (unioning outright would claim `x.f == y.f` on
the `x != y` path), and debit guarded — `pc ? take : 0`. No chunk is merged: ground
never consolidates conditionally-equal addresses.

**Which half of the plan got implemented (a real divergence, not a plan defect).** The
consume model specifies *two* halves: park the whole debit on the demanded chunk as a
guarded negative, **and** read permissions as a guarded Σ-ite,
`avail(x.f) = perm(f(x)) + ite(x==y, perm(f(y)), 0) + …`, so "how much came from each
chunk" is a non-question. That is sound. What we have today is only the first half:
reads consult a *single* chunk, with no alias sum. Parking the debit against that read
path is unsound, and two canaries proved it: after the `1/1` consume, `assert y.f == y.f` wrongly verified
(partner still reading `1/2`), and so did `exhale acc(y.f,1/2)` — the latter never even
reaching the alias fallback, since the partner's own half satisfies the plain proof. So
the debit is instead **distributed greedily across the alias set**, each chunk giving up
`min(holds, still needed)` gated by the pc. That drives every member to its true
remainder, keeps the per-chunk `≥ 0` obligation intact by construction, and needs no
alias probe on subsequent operations.

**These are Silicon's two exhale modes, checked against its source** — not a "real
design" and a "workaround":

- **Greedy (Silicon's default), `ChunkSupporter.consumeGreedy:152`**: `findChunk` resolves
  the address syntactically *or via the prover* (`findChunkWithProver`, which knows
  `x == y` from the path condition), then takes `toTake = PermMin(ch.perm, perms)` from
  that chunk and carries `PermMinus(perms, toTake)` on as the remaining demand. That is
  exactly the distributed `min(holds, still needed)` debit implemented here.
- **`moreCompleteExhale` (opt-in / fallback), `MoreCompleteExhaleSupporter.permSummariseOnly:56`**:
  `permissionSum = PermPlus(permissionSum, Ite(argumentEqualities, ch.perm, NoPerm))`,
  with the value side guarded identically
  (`Implies(And(argumentEqualities, IsPositive(ch.perm)), ?s === ch.snap)`). This is the
  guarded Σ-ite the consume model's step 4 describes.

**Neither mode merges chunks at consume time** — merging lives only in
`StateConsolidator`. For us a merge would be outright wrong: the ground heap is PC-unaware,
so a merged chunk would leak onto the `x != y` path.

So we now match Silicon's default mode. The Σ-ite read side remains worth building (it
never attributes fractions to particular chunks, and it is what Silicon falls back to when
greedy is incomplete), but it is an *alternative* mode rather than a correction of this
one. The four canaries pin the observable behaviour under either.

**Gates:** lib 303/303 both polarities, corpus **29 passing / 12 failing all correct**
(4 new cases: `passing/permissions/pc_alias_consume_sums_halves.vpr` +
`failing/pc_alias_{double_spend,partner_read,partner_double_spend}.vpr`), feature matrix
27/27 with 0 panics, `perf_regression` baseline passes, `structs_enums.vpr` 1.57s vs
1.59s baseline. The probe is only paid when the plain proof fails, so unaliased consumes
cost nothing.

**Still open for S2:** predicate-kind locations (only field chunks are exercised by the
canaries); a symbolic-fraction case (the `min` `ite` folds away for concrete fractions,
so the symbolic path is untested); and the second `Heap` instance from the original plan
is now unnecessary — a single ground heap with guarded distributed debits covers
invariant 7, which is a simplification the pivot bought.

### 2026-07-30 (same session) — S3 measured: invariants 5 and 6 both need restating

**Invariant 6 (statement insts carry block-PC only) — holds, with one exception, and the
exception is fine.** Added `assert_statement_pc_is_block_cube`, gated on
`SILVER_OXIDE_ASSERT_BLOCK_PC` (an env gate rather than `debug_assert`, so it can run in
release over the corpus and matrix — a `debug_assert` compiles out of exactly the runs
that exercise interesting programs). Clean on lib 303, corpus 47 cases, matrix 27/27.

The one violating shape is the one plan 82 predicted, `unfolding p in e` under a ternary:
`pc = [b]` against an empty block cube. But the plan's conclusion — reject the construct
in S1 — does **not** follow from what it actually does. Measured:
`assert (unfolding acc(P(x),1/1) in x.f == x.f)` verifies, a *trailing* `assert x.f == x.f`
correctly fails (so the lowering re-folds: the effect is scoped, not leaked), and a guarded
`unfolding` demanding `1/1` while only `1/2` is held is correctly rejected (no permission
fabrication). So `unfolding` is sound today and merely violates the invariant's letter.
**Rejection not implemented** — it would delete working functionality to satisfy an
invariant that is itself too strong. Behaviour pinned instead by
`passing/predicates/unfolding_expr_scoped_read.vpr` +
`failing/unfolding_expr_{does_not_leak,needs_permission}.vpr`.

**Invariant 5 (extra PC only for expression-embedded side conditions) — empirically
false as written.** New non-gated counters `prove_in_block_{cube_only,extra_pc}` plus a
`#[track_caller]` + `SILVER_OXIDE_TRACE_EXTRA_PC` attribution. On `structs_enums.vpr`:
2652 cube-only vs 205 extra-pc (7%). Across corpus + matrix, every extra-pc obligation
comes from one of three places:

- **115 from `prove_perm_leaves`** (`prove_sufficient` 95, `prove_perm_positive` 20) —
  the suffix is the *held permission's own branch structure*, not an expression guard.
  This is the dominant source and the plan does not mention it. Benign by construction:
  each leaf is proven under exactly the branch that reaches it.
- **8 from the per-inst obligation loop** (`declaration.rs:2774`) — these are the
  expression-embedded ones invariant 5 describes: a `perm(...)` expression under a
  ternary (`conditional_perm_matches_exhale.vpr`) and the guarded `unfolding` above.
- **0 function-precondition or division checks** in this corpus, in-block.

So invariant 5 should be restated as "extra PC comes from expression-embedded side
conditions *or* from the branch structure of a permission being proven per-leaf", and it
is not worth asserting. No perf cost from the instrumentation (1.54–1.57s vs 1.57s;
`perf_regression` passes).

### 2026-07-30 (same session) — S4: flag deleted, dead code removed, plan 82 marked superseded-in-part

**`SILVER_OXIDE_TWO_EGRAPH` is gone.** After the pivot it selected exactly one thing —
invariant 4, unguarded scratch assumes — and measured identical either way (1.55–1.57s
both, same saturation/free-hit/tier-3 counts, 2 rule applications apart). Invariant 4 is
right in principle and free, and it matters more once the scratch is used harder, so it is
now **unconditional** and the knob is deleted rather than left as a flag whose meaning
nobody could state. `scratch_assume_unguarded` carries the reasoning in its doc comment.

**Dead code removed:** `in_two_egraph_block` (unused), `heap_canons` (after framing
returned to ground it was a batched `egraph.find` behind a misleading name — inlined).
`reduce_scratch` + `dirty_reduce` are **kept**: still load-bearing for the tiered scratch
prove. Stale comments corrected — `chunk_under_pc` no longer claims to match in the
scratch, and the `BlockScratch` doc now says imports come from `id_to_node` (the node
minted at that exact uncanonical id) rather than "a ground representative", which is the
distinction the crash turned on.

**Plan 82 now opens with a superseded-in-part table** (crash fixed by id-hygiene not by
construction; invariants 2/3 dropped; 4 unconditional; 5 restated; 6 too strong; 7 needs
one heap; staging status), and the README row points at it. The plan body is kept as
written — its reasoning is still the clearest statement of the model.

**Final state of this branch (all uncommitted):**

- lib **303/303**, also 303/303 with `SILVER_OXIDE_ASSERT_BLOCK_PC=1`
- corpus **33 passing / 17 failing correctly rejected / 1 known-limitation**
  (+1 passing, +3 failing, +1 known-limitation this session beyond the alias four)
- feature matrix **27/27**, and a **78-file panic sweep across corpus + matrix: 0 panics**
- `perf_regression` baseline **passes unchanged**
- `structs_enums.vpr` **1.56s** (baseline 1.59s), `structs_enums_base.vpr` 1.06s
- the original crash repro verifies **59/59 declarations**

**Open, in rough priority order:** (1) the ghost archive — share definitional instances so
per-block re-derivation stops costing ~2×, the one lever left on the two-egraph perf story;
(2) the guarded-Σ-ite perm read side, which would let invariant 7 use the more faithful
parked-negative debit (Silicon's `moreCompleteExhale`); (3) why assuming a PC inflates the
graph ~8× — still unattributed, and it bears on far more than this work; (4)
`known_limitations/perm_sign_from_earlier_conjunct.vpr` — a precondition's earlier conjunct
does not inform a later `acc`'s perm-sign side condition, which Silicon accepts.
