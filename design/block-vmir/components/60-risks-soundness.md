# 60 — Risk register & soundness

## Purpose

Consolidated register of the seams (from the investigation's "Open problems & soundness
caveats" + what we've learned since). Each risk needs a mitigation **or** an adversarial
test to add before the dependent code lands.

## Register

| # | risk | severity | mitigation / test | owner doc |
|---|------|----------|-------------------|-----------|
| 1 | **Extraction soundness** — exporting a representative folded through a local (pc-dependent) union leaks pc into the ghost via term identity | high | RESOLVED by propositions-only export (invariant 1). **Add adversarial test** pinning it; ban "optimize export via local graph" in review | 20 |
| 2 | **Inconsistent locals** leak value-collapse / garbage heap into the ghost | high | dead branch exports only its guard's falsity; nothing else. Test: infeasible-cube block exports no spurious equality | 20, 50 |
| 3 | **Heap residency / id-mapping** unspecified; translation churn erodes the win | ~~high~~ **low (RESOLVED 2026-07-26)** | `[50]`: heap ghost-resident, locals read+prove only, perm = guarded Σ-ite, consume = single-chunk pc-guarded debit (no split/merge). **Residual:** measure per-block translation cost (go/no-go) + recipe survival (U6) | 50 |
| 4 | **Ghost fork = deep copy** cost | med | accepted (ghost small; codebase already clones full graphs). Fallback: overlay memo (`7eec230`). Measure if fork copies dominate | 20 |
| 5 | **Export-selectivity** — under-export ⇒ later blocks can't prove things that worked; over-export ⇒ pollution returns | ~~high~~ **med (base set decided 2026-07-26)** | base set = **Viper-explicit assumes only**; asserts not exported (enablable flag); rest re-derivable (`[20]`). **Regression empirically extreme**: "same fact both arms" telescopes free at the join (0 splits, even NO_TIER4 — `underexport2.vpr`); the genuine residual (unconditional fact provable only by case-split) is the **Z3-residue class**, Z3-owned regardless of export policy → not-exporting-asserts is a **perf/Z3-load knob, not a completeness cliff** (given Z3; without Z3 = today's NO_TIER4). **Keep a canary.** | 20 |
| 6 | **Footprint divergence at joins** — location held in some arms only → real `0` arm, structural collapse can't apply | ~~high~~ **med (SUBSUMED 2026-07-26)** | **not a distinct failure mode** — it's the conditional cousin of the give-back: represented by `[50]` Σ-ite per-edge guarded chunks → persistent conditional perm (U4); sound divergence is always *conditionally demanded* (else a Viper perm error); sufficiency `ite(edge,p,0) ≥ ite(demand,need,0)` discharges when guards share a class (join telescope + T1), residual = **same exhaustiveness bridging → Z3**. Measured: `divergent.vpr` = 1 split, fails NO_TIER4 (identical signature to give-back). **Rare** (Prusti uniform result-places). Join rule in `[30]`; keep canary | 30, 50 |
| 7 | **Loops / back-edges** — design is DAG-shaped | med | deferred to M5; IR (`[10]`) must not preclude (block graph not DAG); invariants + havoc story later | 10, 70 |
| 8 | **Cert / recipe machinery** assumes one live graph — FunctionDefinition/ResourceDefinition, recipe grafting, recursive-fn post facts (limited symbols) | ~~high~~ **low (MAPPED 2026-07-26)** | functions/resources ride the same local-prove / ghost-guarded-proposition / replay discipline as heap chunks — see `[20]` §"Functions & resources propagation": production=local, storage=ghost archive (success-gated, recursive post-facts ghost-wide via `f'`), replay=ghost instantiating tier, pre-token = the "looks wrong" artifact. **Residuals only:** recipe survival (U6) + graft id-translation | 20, 50 |
| 9 | **Quantifier scoping** — ghost instantiates unconditional foralls only; locals instantiate under cube, instances die/export guard-wrapped (fixes branch-pollution). Matching-loop risk moves into the **persistent** ghost | med | hard instantiation budget/depth bound as a **design requirement**; WD via graph-clone runs in a declaration-scope local | 20 |
| 10 | **Generator ≠ Prusti** — rule/shape conclusions from `gen_enum_match.py` may not match real Prusti output (already seen: lt-ite load-bearing on generator, not on Prusti mut case) | med | validate every rule/collapse claim on a real Prusti dump, not only the generator | 40, 30 |

## Soundness one-liners (keep true)

- Guarded exports: golden rule. Forgetting: weakening. Locals: discarded. Ghost:
  globally-true, pc-less, monotone. Trigger matching: congruence, never normal form.

## Adversarial tests to add (checklist)

- [ ] pc-leak canary (risk 1): a local-only equality must **not** appear in a later block.
- [ ] infeasible-cube export canary (risk 2).
- [ ] under-export regression canary (risk 5): a fact provable today that must remain
  provable after localization.
- [ ] footprint-divergence case (risk 6), ideally Prusti-generated.
- [ ] matching-loop budget canary (risk 9): tag()-style self-feeding axiom bounded.

## Status

seeded — **no high-severity design-sink risk remains.** 3 resolved (`[50]`), 6 subsumed
(`[30]`/`[50]`), 8 mapped (`[20]`), 5 base-set-decided (perf/Z3 knob, `[20]`). What's left
is mitigations-with-canaries (1, 2, 9), an accepted cost (4), a deferred feature (7 loops),
and a validation discipline (10) — plus the actual undesigned *components* ([10] block IR,
live-cone extraction), which are build work, not register risks.
