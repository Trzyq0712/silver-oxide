# Block-VMIR — progress log

Running, between-sessions record of the block-structured VMIR effort (branch
`backend-blocks`). Newest entry on top. Design in this tree (`README.md`, components 10–70);
staged build plan in `80-implementation-plan.md`. One entry per work session — what landed,
key decisions, test state, what's next.

Milestone shorthand (from `80`): **M1** block IR + block walker (no-op refactor) → **M3**
structural joins (tier-4 killer) → **M4** rule diet. v1 = single ground e-graph, no
local/ghost fork/remap.

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
