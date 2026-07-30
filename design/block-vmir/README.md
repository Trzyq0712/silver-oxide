# Block-based VMIR + local/ghost e-graphs — design & planning hub

**Status:** implementation underway (`backend-blocks`). This tree holds the component design
docs, the staged build plan (`80-implementation-plan.md`), and a between-sessions
**[PROGRESS.md](PROGRESS.md)** log (newest on top — read it first to see where we are).

**Goal:** verify Prusti-generated Viper **without tier-4** and **faster**, by replacing
the CFG-linearized VMIR + monolithic e-graph with a **block-structured VMIR** executed
over **per-block local e-graphs** backed by a **ghost archive**, so that branch
structure is preserved and joins collapse permission partitions **structurally**.

---

## Why (the case, in one screen)

Established by the analysis in `~/.claude/plans/let-s-have-a-serious-abundant-sphinx.md`
and memory `project_exit_perm_representation_gap`, verified on current `backend`
(2026-07-25):

- The remaining enum-`match`/`&mut` failure is a **representation gap, not a
  recognition gap**. Exhaustiveness (`exhale false` on the dead default arm) already
  discharges tier-4-free. The **only** failing goal is the exit `exhale …#ensures 1/1`
  — full perm for the give-back/return at the join. It fires tier-4 **exactly once**
  per method exit (uniform across every mut-through-match / owned-return case).
- Cause: the **value** phi at a join is built exhaustive-edge / last-arm-unguarded
  (`build_entry_env`, `reach.rs:193`) → no fall-through leaf → collapses. The **perm**
  does not use that phi; it accumulates in the linearized heap as scaled exhale/inhale
  → `Σ ite(flag_k, 1/1, 0)` with a **`0` fall-through**. That `0` leaf is the blocker.
- **Block-based joins route perm through the same exhaustive-edge phi as values** →
  the exit perm collapses to `1/1` structurally, no positive-partition proof, no Z3,
  no tier-4. The give-back cancellation already leaves each arm at `1/1`.
- Bonuses: eliminates the monolithic-graph growth (locals discarded), gives
  Silicon-style dead-path pruning for free (inconsistent local → skip block), and
  fixes the accepted quantifier branch-pollution unsoundness structurally.

VMIR is **no longer quadratic** (fixed `1b53e98`), so IR bloat is off the table; this
work is about **structure and reasoning locality**, not inst count.

---

## Non-negotiable invariants (soundness spine — protect in every component)

1. **Exports carry propositions, not e-graph state.** Local→ghost exports are the
   *as-written* asserted/assumed facts wrapped with the block's (static, exact) pc.
   Nothing the local *derived* crosses the boundary. Any "optimize export using the
   local graph" idea reintroduces the pc-leak hazard and is banned without a
   ghost-valid-equality walk. Adversarial export-pinning test is mandatory.
2. **Ghost facts are globally true, pc-less.** Exports are guard-wrapped at export
   time; the ghost never carries a live pc. Branch ghosts fork for isolation only;
   join = plain delta union (sound in any order).
3. **Locals assume their block pc unconditionally, and are discarded at block exit.**
   That is where obligation-discharge performance lives (flags become constants).
4. **Joins are built exhaustive-edge (last arm unguarded), for perm as well as value.**
   No manufactured `0`/fall-through leaf at a real CFG join. This is the structural
   collapse; it must never depend on a proof.
5. **Trigger matching depends on congruence, never on reductive normal form**
   (`reference: project_triggers_no_inference`, investigation §trigger-contract).

---

## Component map

Fill order roughly top-to-bottom; `[10]` and `[40]` are the two the supervisor flagged
for early deep evaluation. Each doc follows the same skeleton (Purpose / Current
understanding / Open decisions / Sketch / Risks / Depends-feeds / Status).

| # | doc | decides | depends on | status |
|---|-----|---------|-----------|--------|
| 10 | [components/10-block-vmir-ir.md](components/10-block-vmir-ir.md) | block-structured VMIR: blocks, terminators, phi, per-block pc, heap threading | — | **sketched (2026-07-26)**: join-source form (no terminators), join/body phases, SSA kept, pc split, v1 single-e-graph; needs Rust types + perm-AST |
| 20 | [components/20-verifier-local-ghost.md](components/20-verifier-local-ghost.md) | local-per-block + ghost archive; seeding from live cone; rule tiers; discard | 10 | **fn/resource propagation + export rule + fork/merge-remap resolved (2026-07-26)**; live-cone extraction open |
| 30 | [components/30-joins-reachability.md](components/30-joins-reachability.md) | exhaustive-edge join for value+perm+heap; feasibility prune; dead-block skip | 10, 20 | **join = structural merger (no rewrite rules); read-off; dead-arm Route 1 decided 2026-07-26**; full join-algorithm sketch open |
| 40 | [components/40-rewrite-rules.md](components/40-rewrite-rules.md) | which rules survive; local-only/reductive/instantiating tiers; lt-ite fate | 20, 30 | **perm-merge = 0 rewrite rules (structural, 2026-07-26)**; survivor→tier table firm at M3 |
| 50 | [components/50-heap-residency.md](components/50-heap-residency.md) | chunk value/perm as ghost vs local ids; id-mapping across blocks | 10, 20, 30 | **resolved** + **perm is explicit term, not e-class (2026-07-26)**; opens are measurements |
| 60 | [components/60-risks-soundness.md](components/60-risks-soundness.md) | consolidated risk register + adversarial tests; loops; certs/recipes; quantifiers | all | **no high-severity design-sink risk remains** (see register) |
| 70 | [components/70-migration-gates.md](components/70-migration-gates.md) | incremental migration, kill switches, benchmarks, go/no-go gates | all | seeded |
| 80 | [80-implementation-plan.md](80-implementation-plan.md) | **staged v1 build plan** (single ground e-graph; M1→M3, skips M2) | all | **assembled 2026-07-26** |
| 81 | [81-stage4-implementation.md](81-stage4-implementation.md) | **Stage 4 code-level guide** (ChunkPerm storage, merge_heaps, dead-arm) — for the implementing agent | 10,30,50,80 | **written 2026-07-27** (pre-impl) |
| 82 | [82-two-egraph-block-model.md](82-two-egraph-block-model.md) | two-egraph exec (ground+scratch); 7 invariants; stages S1–S4. **Read its superseded-in-part header first**: crash fixed by id-hygiene (not by construction), invariants 2/3 dropped for a ground-first hybrid, 5 restated, 7 needs only one heap | 20,30,50 | **implemented + partly overturned 2026-07-30** — see PROGRESS.md |

---

## The process (how we fill this in)

Iterate, don't waterfall. Per session:

1. Pick a component (or a seam that spans two). Bring its **Current understanding** up
   to date with any new measurement.
2. Turn one **Open decision** into a **Sketch** (concrete: types, pseudo-code, a worked
   example on the enum case). Prefer measuring over asserting — the repo has
   `SILVER_OXIDE_*` ablation flags and generators; use them.
3. Log new **Risks** and, for each, either a mitigation or an adversarial test to add.
4. **Consistency pass:** reconcile the touched component with its `depends-on`/`feeds`
   neighbours and with the invariants above; update this README's status column.
5. When a component's Open decisions are all Sketched and neighbour-consistent, mark it
   `ready`; when all are `ready`, the implementation plan (a separate `~/.claude/plans`
   doc) is assembled from the sketches.

Definition of done for *this planning tree*: every Open decision has a Sketch, every
Risk has a mitigation-or-test, the go/no-go gates in `70` are runnable, and no
cross-component gap remains.

---

## Milestones (coarse, revisable)

- **M0 — de-risking on-ramps (optional, parallel):** goal-cone saturation
  (`context.rs run_probe` seed from goal cone) + `V1` canonicalize-on-store. IR-free,
  proves local-discharge mechanics, buys N without the paradigm change.
- **M1 — block VMIR:** stop linearizing; emit block-structured VMIR (10). Verifier
  still runs one graph but walks blocks in topo order. No behaviour change target: green.
- **M2 — local/ghost split:** per-block local seeded from ghost; obligations discharge
  in local; propositions-only export (20). A/B per declaration via kill switch.
- **M3 — structural joins:** exhaustive-edge perm/heap merge + dead-block skip (30) →
  the exit-perm goal collapses without tier-4. Target: `NO_TIER4` green on enum family.
- **M4 — rule diet:** demote/remove linearization-era rules once locals make their
  goals ground (40); lt-ite first candidate. Measured, gated.
- **M5 — harden:** loops, certs/recipes, quantifier scoping, migration cleanup (60/70).

---

## Go/no-go gates (from the investigation; runnable form in `70`)

- Live-cone size at block entry **O(1)/arm**; export-delta at block exit **O(1)/arm**
  on the enum benchmark ⇒ total cost linear.
- `structs_enums.vpr` 305/305 with `SILVER_OXIDE_NO_TIER4=1`.
- Enum `match` scales to N=20, N=100 with no arm-count cliff.
- `cargo test --lib` + corpus green throughout; quantifier goals unchanged.

---

## Ground-truth facts established (don't re-derive)

Measured on `backend`, 2026-07-25 (release `verify`):

- VMIR no longer quadratic (`1b53e98`): heap-free elseif N=64 12,420→323 insts.
- `gen_enum_match.py 8`, `NO_TIER4`: only failure = exit `exhale m_add#ensures 1/1`;
  `bb_unreach: exhale false` passes; `prove_splits: 0` elsewhere. With tier-4:
  `prove_tier4: 1, prove_splits: 1` (the sole split).
- Every mut-through-match / owned-return case = **exactly 1 tier-4 split** (the exit),
  independent of arm count. Nesting **without** give-back (`option_like__match_nested`)
  = **0 splits**.
- Nested match on the **same value** (`unreachable!()` arms) discharges trivially:
  dead-arm pc `a==i ∧ a==j` is a direct const-fold contradiction; 0 splits, 33 nodes.
- **lt-ite**: services the `perm ≥ 0` side-condition on scaled perms `c ? p : 0`.
  `NO_LTITE + NO_TIER4` on `enum_clike__mut_through_match` → FAIL "permission may be
  negative". `NO_LTITE` alone → tier-4 splits 1→5 (tier-4 compensates; lt-ite is a
  sufficiency perf-multiplier there). Real Prusti mut case passes without it (tier-4
  covers); the flat `gen_8` generator needs it. eq-ite (`NO_EQITE`) not load-bearing
  on these. Flags: `SILVER_OXIDE_NO_LTITE / NO_EQITE / NO_DISTRIB / NO_TIER4`.

## Source anchors

- Linearizer / reach: `src/translate/reach.rs`, `src/translate/decl/method.rs`,
  `src/translate/sink.rs` (value-numbering memo).
- Heap / chunks: `src/verify/heap.rs`; merge/subtract: `src/verify/declaration.rs`
  (`merge_chunks:564`, `heap_union:817`, `heap_subtract:992`, `prove_perm_ineq:881`).
- Collapse helpers: `src/verify/context.rs` (`merge_ite_sum:837`, `flatten_plus:845`,
  `merge_summands:885`, `prove_under_pc:481`).
- Rules: `src/verify/rewrite.rs` (`distributive_ite_rules:436`, `lt-ite:481`,
  `terminating_ite_rules / ite-reduce:530`).
- Related memory: `project_ghost_local_egraphs`, `project_heap_ternary_join_select`,
  `project_exit_perm_representation_gap`, `project_perm_collapse_root_cause`,
  `project_reach_dnf_pc`, `project_quantifier_branch_pollution`.
