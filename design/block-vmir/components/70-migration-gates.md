# 70 — Migration, kill switches, and go/no-go gates

## Purpose

How we get from today's monolithic linear verifier to block-based **incrementally**,
without breaking the 304/305 baseline, and how we decide at each step whether to
continue.

## Current understanding (decided)

- **Ghost = current graph, unchanged.** Add locals block-by-block; route obligations;
  A/B per declaration behind a kill switch. Migration is additive, not a rewrite.
- Kill-switch precedent exists (`SILVER_OXIDE_NO_TIER4`, context.rs:528; the
  `NO_LTITE/NO_EQITE/NO_DISTRIB` ablations). Add `SILVER_OXIDE_BLOCK_LOCAL` (per-decl
  opt-in) so the two engines run side-by-side and diff.
- Tier-4 stays until M3 proves the structural join removes its sole goal; then M4
  removes it + the linearization-era rules, measured.
- **v1 execution reuses ONE shared ground e-graph** (no per-block local, no ghost fork/
  merge, **no enode-id remap**) through M1–M3 — decided 2026-07-26, `[10]`. This is the
  simplest path and sidesteps the id-mapping seam entirely. **The tier-4 killer does not
  need forking:** the perm structural-merge is over *explicit* terms + binary-join
  `ite`-collapse, so M3 can go `NO_TIER4`-green on one e-graph. **Forking + isolation +
  remap (`[20]`/`[30]`) is the LATER step** — the value e-node *scaling* story, slotting
  into the join phase only. So M2's "local/ghost split" is **re-scoped as optional/later**:
  the correctness win (tier-4 removal) lands in v1 without it.

## Milestone gates (each must pass before the next starts)

- **M0 (on-ramps, optional):** goal-cone saturation + `V1`. Gate: benchmark time drops,
  suite green, no soundness change. Pure win or skip.
- **M1 (block VMIR, `[10]`):** emit blocks; verifier walks them in topo order over the
  **same single graph**. Gate: **byte-for-byte same verification results** (305/305,
  same tier-4 count) — a no-op refactor. If results move, the block lowering is wrong.
- **M2 (local/ghost, `[20]`+`[50]`):** obligations discharge in per-block locals;
  propositions-only export. Gate: suite + corpus green **with `BLOCK_LOCAL` on**;
  pc-leak + infeasible-export canaries pass; live-cone O(1)/arm on the enum benchmark.
- **M3 (structural joins, `[30]`):** exhaustive-edge perm/heap merge + dead-block skip.
  Gate: **`NO_TIER4` green on the enum family**; the exit-perm goal collapses with no
  split; export-delta O(1)/arm; N=20/100 no cliff.
- **M4 (rule diet, `[40]`):** demote/remove lt-ite/eq-ite/`merge_ite_sum`/tier-4,
  one at a time, ablation-gated. Gate: each removal keeps suite+corpus green and
  doesn't regress time; verdicts recorded in `[40]`.
- **M5 (harden, `[60]`):** loops, certs/recipes, quantifier budget, cleanup.

## Go/no-go metrics (runnable)

- `SILVER_OXIDE_TRACE_SIZE` — per-inst node/class counts; plot with
  `scripts/plot_egraph_size.py`. Track live-cone (block entry) + export-delta (block
  exit) size vs arm count: both **O(1)/arm** ⇒ linear total.
- Benchmark: `structs_enums.vpr` 305/305, target ≤ ~Silicon's marginal times, base
  unchanged. Enum `gen_enum_match.py {20,100}` verify.
- `cargo test --lib` + corpus green at every milestone; quantifier goals unchanged.

## Reproduce (baseline harness)

```bash
python3 tests/cases/gen_enum_match.py 18 > /tmp/gen_18.vpr
SILVER_OXIDE_TRACE_SIZE=/tmp/t.csv cargo run --release -q --bin verify -- /tmp/gen_18.vpr
SILVER_OXIDE_NO_TIER4=1 cargo run --release -q --bin verify -- <case>
cargo test --lib
```

## Open decisions

- Diff harness for M1/M2 A/B (same-graph vs block-local) — automatic result compare
  across the corpus, or manual per-decl?
- Do M0 on-ramps land on `backend` first (independent value) or fold into M2?

## Depends on / feeds

Depends on all. This is the schedule spine; `README.md` milestones mirror it.

## Status

seeded — M1's "no-op refactor" gate is the key early de-risk; define the A/B diff
harness first.
