# 81 — Stage 4 implementation guide (structural heap merge, the tier-4 killer)

**Audience:** the agent implementing Stage 4. Read `80-implementation-plan.md` (staging),
`components/30-joins-reachability.md` (join semantics), `components/50-heap-residency.md`
(perm representation) first. This doc is the concrete code-level plan: types, signatures,
pseudocode, and the exact seams in the current tree. Branch `backend-blocks`.

Milestone: **M3** (the enum exit perm collapses without tier-4). All work is gated behind a
flag so Stage 3 stays the byte-identical oracle until 4.4.

---

## 0. Where we are (Stage 3 recap, with line anchors)

- Heap threads **linearly** in the lowering (`src/translate/decl/method.rs::lower_method`):
  `current_heap` flows block→block; `h_in = current_heap` (`:323`), `h_out = current_heap`
  (`:539`). `Preds::Join` is recorded but **dormant**; no heap is merged at a join.
- Arms are made interference-free by **`gate_perm`** (`src/translate/sink.rs:142`) — every
  in-arm `Combine`/resource perm is `ite(reach, amt, 0)`. Field writes use **`gate_value`**
  (`sink.rs:202`). This is what produces the additive `Σ ite(flag,1/1,0)` tower with the
  `0` leaf at the exit exhale = the one tier-4 split.
- Verify side (`src/verify/declaration.rs`): `Chunk.perm: egg::Id` (`heap.rs:41`); the heap
  ops are `merge_chunks:564`, `heap_union:817`, `heap_subtract:992`,
  `find_chunk_consolidated:766`, `eval_heap_inst:1108`. `HeapInst::Merge` returns
  `Unimplemented` (`declaration.rs:1117`). Walker: `verify_method:2438`, per-block
  Stage-4 hook comment at `:2470`.

Stage 4 replaces the linear thread + gating with: **fork arms → run unguarded → SELECT at
the join**.

---

## 1. Flag (Stage 4.0)

Add `SILVER_OXIDE_BLOCK_MERGE` (env-var bool, default OFF), read once into a `Program`- or
`VerifyContext`-level flag AND a lowering-level flag (both sides must agree — the lowering
stops gating, the verifier starts merging). Follow the existing `SILVER_OXIDE_NO_TIER4`
pattern (see `context.rs` / `stats.rs` flag plumbing). With the flag OFF everything below is
inert: perms are `Leaf`, `to_id` is identity, lowering still threads `current_heap` + gates,
`Merge` is never emitted. **4.0 gate: `cargo test` unchanged.**

---

## 2. Perm storage: `ChunkPerm` (Stage 4.1)

### 2.1 The type (`src/verify/heap.rs`)

```rust
/// A chunk's permission as an explicit term, held OUTSIDE the union-find.
/// `Leaf` values are e-class ids; only the join merge builds `Select`.
#[derive(Debug, Clone)]
pub enum ChunkPerm {
    /// An amount straight from the e-graph: a literal (`1/1`), a symbolic real,
    /// a wildcard-bearing term, OR a program-written `c ==> acc` gated `ite`.
    /// OPAQUE — never structurally decomposed. (User-written conditionality that
    /// Viper already put in the assertion stays here; design 50 / user note.)
    Leaf(egg::Id),
    /// A control-flow join select `cond ? then : els`, built ONLY by the merge.
    /// The explicit structure that lets give-back collapse without saturation.
    Select { cond: egg::Id, then: Box<ChunkPerm>, els: Box<ChunkPerm> },
}
```

`Chunk.perm` changes `egg::Id → ChunkPerm`. `Chunk::new(addr, perm, value)` takes a
`ChunkPerm`; most call sites pass `ChunkPerm::Leaf(perm_id)`.

### 2.2 Smart constructors + lowering (`heap.rs` or a new `perm.rs`)

```rust
impl ChunkPerm {
    fn leaf(id: egg::Id) -> Self { ChunkPerm::Leaf(id) }

    /// Structural equality of two perm terms with LEAVES compared by e-class
    /// `find` (so `1/1` from either arm is "equal"). O(size), no saturation.
    fn same(ctx: &VerifyContext, a: &ChunkPerm, b: &ChunkPerm) -> bool {
        match (a, b) {
            (Leaf(x), Leaf(y)) => ctx.egraph.find(*x) == ctx.egraph.find(*y),
            (Select{cond:c1,then:t1,els:e1}, Select{cond:c2,then:t2,els:e2}) =>
                ctx.egraph.find(*c1) == ctx.egraph.find(*c2)
                && Self::same(ctx,t1,t2) && Self::same(ctx,e1,e2),
            _ => false,
        }
    }

    /// The join select smart constructor. `cond` is the then-edge reach value.
    /// Applies, in order:
    ///   (i)  same-amount collapse: then ≡ els  ⇒  then       (give-back / untouched)
    ///   (ii) dead-arm drop under the join block's assumed context:
    ///        cond folds true  ⇒ then ;  cond folds false ⇒ els
    ///   (iii) otherwise Select{cond, then, els}
    /// Deterministic, bounded, no budget. Rule (ii) uses ONLY the ground e-graph's
    /// const-fold (no assume) — see §5; the join block's cube is already assumed in
    /// the graph by the time the merge runs (the walker assumed the block's own pc).
    fn select(ctx: &mut VerifyContext, cond: egg::Id, then: ChunkPerm, els: ChunkPerm) -> Self {
        if Self::same(ctx, &then, &els) { return then; }
        match ctx.egraph[ctx.egraph.find(cond)].data.known() {
            Some(Literal::Bool(true))  => return then,
            Some(Literal::Bool(false)) => return els,
            _ => {}
        }
        ChunkPerm::Select { cond, then: Box::new(then), els: Box::new(els) }
    }

    /// Lower to an e-graph id — ONLY where the prover needs an e-class
    /// (sufficiency, bound/non-alias axioms, `perm > 0` framing). Never called
    /// to inspect shape.
    fn to_id(&self, ctx: &mut VerifyContext) -> egg::Id {
        match self {
            Leaf(id) => *id,
            Select{cond,then,els} => {
                let t = then.to_id(ctx); let e = els.to_id(ctx);
                ctx.add(Symbolic::Ite([*cond, t, e]))
            }
        }
    }

    fn has_wildcard(&self, ctx: &VerifyContext) -> bool { /* walk, reuse contains_wildcard on leaves */ }
}
```

### 2.3 Migrating the existing heap ops (flag-OFF = identity)

- **`merge_chunks` (`:564`)** — this is the *aliasing* Σ (same-state, additive), **NOT** the
  control-flow join. It stays additive. Change its perm handling to:
  `perm = ChunkPerm::Leaf(ctx.add(AddR[p0.to_id(), p1.to_id()]))` then the existing
  `merge_ite_sum` collapse on that id. Value/agreement axiom unchanged. (Aliasing perm never
  needs `Select` — keep it a `Leaf`.)
- **`heap_union` / `heap_subtract` / `find_chunk_consolidated`** — read `existing.perm` via
  `.to_id(ctx)` wherever they currently use `existing.perm` as an id (the `AddR`, the
  `LtR` sufficiency goal, the `SubR` remainder, the wildcard path). Store results back as
  `ChunkPerm::Leaf(...)`. Mechanical.
- **`assume_location_axioms` / `location_chunks` (`:640`)** — `LocationChunk.perm` uses
  `chunk.perm.to_id(ctx)`.
- **wildcard exhale (`:1022`)** — `contains_wildcard` on `chunk2.perm.to_id(ctx)`; wildcard
  perms stay `Leaf`, never enter a `Select`.
- **`empty` drop test (`:1090`)** — const-fold on the `SubR` remainder id, unchanged.

**4.1 gate:** flag OFF ⇒ every perm is `Leaf`, `to_id` is identity ⇒ byte-identical to
Stage 3. `cargo test --lib` + corpus + perf all green. Commit here.

---

## 3. Fork + `Merge` emission — lowering (Stage 4.2, `translate/decl/method.rs`)

Behind the flag. The linear `current_heap` thread becomes a **per-block `h_in` derived from
`Preds`**, and arms stop gating.

### 3.1 `h_in` derivation

Maintain `h_out: TiVec<vmir::BlockId, HeapVal>` as blocks are pushed. For each block:

```
h_in = match preds_kind {
    Preds::Entry            => baseline,                  // post-#requires-inhale entry heap
    Preds::From(p)          => h_out[p],                  // single pred: inherit
    Preds::Join{cond,then_,els} => {
        // emit into the JOIN phase, before the phis:
        let h = sink.emit_heap(HeapInst::Merge { cond, then_h: h_out[then_], els_h: h_out[els] });
        h                                                 // a fresh HeapVal::Temp
    }
};
```

The block body then lowers against `h_in` instead of the threaded `current_heap`; `h_out`
for this block = the heap after the body. Synthetic n-ary join blocks (`:444`) emit a
`Merge` too (they already carry `h_out: h_in` today → becomes `h_out: <the Merge result>`).

### 3.2 Stop gating in arms

- `gate_perm` (`sink.rs:142`): under the flag, return the perm **unchanged** (arms run under
  the assumed block cube → literal amounts). Keep the wildcard-structural path only if a
  wildcard is present (wildcards still need the `ite` form even unguarded? — no: unguarded
  means bare `Wildcard`; verify). The empty-pc path already returns unchanged, so flag-ON is
  "always the empty-pc branch."
- `gate_value` (`sink.rs:202`): under the flag, return `val` unchanged — the join's value
  phi (`merge_two_envs` + the `Merge`'s value select) now carries the branch, so a field
  write inside an arm must NOT also gate. **This is the subtle one** — a field assign in an
  `if` arm writes the arm heap unconditionally; the merge selects the written vs untouched
  value at the join. Canary: `narrowing_*`, assignment corpus.

**Watch:** `current_heap` is also used for `old`-heap capture (`labeled.insert(l,
current_heap)` `:463/775`) and baseline. Under the fork model these must capture the correct
per-block heap (the block's `h_in`/working heap), not a linear cursor. Thread explicitly.

### 3.3 Verify-side `merge_heaps` (`declaration.rs`)

```rust
/// Structural control-flow SELECT merge of two predecessor exit heaps at a binary
/// join. Runs with the join block's cube ALREADY assumed in `ctx` (the walker
/// assumed the block pc before calling), so a chunk's full-cube guard has already
/// const-folded to the edge. Per group, per address.
fn merge_heaps(
    ctx: &mut VerifyContext<'_>,
    cond: egg::Id,            // the then-edge reach value (Preds::Join.cond, evaluated)
    h_then: &Heap,
    h_els: &Heap,
    pc_lits: &[(egg::Id, Polarity)],
) -> Heap {
    let mut out = Heap::empty();
    // Union of (kind) groups present in either arm.
    for kind in h_then.kinds().chain(h_els.kinds()).dedup() {
        // Address identity by e-class find; alias via congruence. Collect the union
        // of addresses across both arms (canonicalize with ctx.egraph.find).
        for addr in union_of_canonical_addrs(ctx, h_then, h_els, kind) {
            let ct = h_then.chunk_canon(ctx, kind, addr);   // Option<&Chunk>
            let ce = h_els .chunk_canon(ctx, kind, addr);
            let chunk = match (ct, ce) {
                (Some(a), Some(b)) => {
                    // Both hold it. SELECT perm; equal ⇒ bare constant (the kill).
                    let perm  = ChunkPerm::select(ctx, cond, a.perm.clone(), b.perm.clone());
                    // Value phi: ite(cond, va, vb), collapses via existing eq-union.
                    let value = ctx.add(Symbolic::Ite([cond, a.value, b.value]));
                    Chunk::new(addr, perm, value)               // recipe: None (ghost-built)
                }
                // Divergent footprint: held on ONE edge only ⇒ ite(cond, p, 0) or
                // ite(cond, 0, p). Genuinely conditional held perm (U4). If the
                // absent side is a DEAD arm, `select` already dropped it (§5).
                (Some(a), None) => {
                    let zero = ChunkPerm::Leaf(zero_real_id(ctx));
                    let perm = ChunkPerm::select(ctx, cond, a.perm.clone(), zero);
                    Chunk::new(addr, perm, a.value)
                }
                (None, Some(b)) => {
                    let zero = ChunkPerm::Leaf(zero_real_id(ctx));
                    let perm = ChunkPerm::select(ctx, cond, zero, b.perm.clone());
                    Chunk::new(addr, perm, b.value)
                }
                (None, None) => continue,
            };
            out = out.with_chunk(kind, chunk);
        }
    }
    assume_location_axioms(ctx, &out);       // bounds / non-alias over the merged sum
    out
}
```

Helpers to add on `Heap` (`heap.rs`): `kinds()` (iterate group keys), `chunk_canon(ctx,
kind, addr)` (find by canonical e-class, reusing the `find_chunk_consolidated` matcher).
`union_of_canonical_addrs` walks both arms' chunks, canonicalizes `addr` with
`ctx.egraph.find`, dedups.

**Key invariants (do not violate):**
- SELECT across arms, never `+`. Summing edge-guarded arm chunks double-counts and rebuilds
  the tower (design 30).
- `cond` is the *edge* value; because the block cube `X` is assumed, `X && d` is already `d`
  in the graph, so the select keys on `d` alone. Do not re-wrap with `X`.
- Give-back leaves each arm at a bare `1/1` (the in-arm `(x−1)+1 ⇒ x` add-sub-cancel already
  fired unguarded) ⇒ `same()` is true ⇒ constant, `cond` dies.

### 3.4 `eval_heap_inst` Merge arm (`declaration.rs:1117`)

```rust
HeapInst::Merge { cond, then_h, els_h } => {
    let cond_id = state.get_val(ctx, cond);
    let h_then  = get_heap(state, then_h);
    let h_els   = get_heap(state, els_h);
    let pc_lits = collect_pc_lits(ctx, state, pc);   // the block cube
    Ok(merge_heaps(ctx, cond_id, &h_then, &h_els, &pc_lits))
}
```

`Merge` is a `Heap` inst → `push_heap`s its result (the walker already does this for heap
insts). No cube needs separate threading: the walker assumed the block pc before the join
phase runs, so the const-folds in `select` see it.

**4.2 gate:** with flag ON, `gen_enum_match 8` verifies under `SILVER_OXIDE_NO_TIER4=1`
(`prove_splits: 0`), and normally. Commit.

---

## 4. Value merge note

`merge_two_envs` (`reach.rs:197`) already builds the value phi `ite(cond, vA, vB)` for
variables that differ across arms — that stays. The heap `Merge` builds the *chunk value*
select (§3.3) for held locations. With `gate_value` off, a field write in an arm is
unconditional in that arm's heap; the merge's `ite(cond, a.value, b.value)` reconciles it.
The two value paths (env phi for locals, chunk-value select for heap) are consistent — both
key on the same edge `cond`.

---

## 5. Marking blocks unreachable (Stage 4.3)

**The simplification: detection == join elimination == one const-fold. No dead-block flag in
v1.** A dead arm's edge `cond` folds `false` in the ground e-graph; `ChunkPerm::select` rule
(ii) drops it; its `h_out` is never selected. "Mark unreachable" ≡ "edge folds false."

- **Detection (const-fold only, no assume, no clone):** query
  `ctx.egraph[ctx.egraph.find(cond)].data.known()`. `Some(Bool(false))` ⇒ the then-arm edge
  is infeasible; `Some(Bool(true))` ⇒ the els-arm edge is. This catches the measured
  same-value `unreachable!()` case (`a==i ∧ a==j` is a direct congruence/const-fold
  contradiction). **Do NOT `assume` the cube into the ground graph to test it** — the single
  v1 graph would be globally poisoned (everything discharges → unsound).
- **Body-skip (perf layer, optional in 4.3):** in the walker, before walking a block's body,
  if the block's *edge into it* has folded false (all incoming edges infeasible), skip the
  body — its obligations are vacuous and skipping keeps dead facts out of the ground graph.
  Mark `h_out` a dead sentinel (e.g. `Heap::empty()` tagged, or track a `dead: BitSet` over
  block ids). The consuming join drops the dead arm via the same fold. **For 4.3 minimal:
  rely on `select`'s rule (ii) alone** (the merge drops the dead arm's chunks); add body-skip
  only if a benchmark shows dead-fact pollution.
- **Escalation (not needed for the target family):** deeper feasibility (a contradiction the
  const-fold can't see without assuming) → scratch-clone test (`clone` the egraph, assume the
  cube, check `is_inconsistent()`, discard — the mechanism `prove_under_pc` already uses at
  `context.rs:481/518`). Behind the prover, off the hot path.

**Route-1 payoff:** a *divergent* join whose divergent side is the dead arm has **no `0`
leaf** — `select(cond, p, 0)` with the `0`-side edge folded false collapses to `p`.

**4.3 gate:** nested-`unreachable!()` cases discharge with 0 splits (as on `backend`); no
corpus regression.

---

## 6. Scale + flip (Stage 4.4)

- `gen_enum_match {20, 100}`: no arm-count cliff, `NO_TIER4` green.
- Flip `SILVER_OXIDE_BLOCK_MERGE` default ON.
- `structs_enums.vpr` 305/305 with `NO_TIER4`.
- `cargo test` (lib + suite + perf_regression) green; refresh `benchmarks/baseline/*` via
  `UPDATE_PERF_BASELINE=1` and review the cost diff (should DROP — the tier-4 split is gone).
- Remove the now-dead `gate_perm`/`gate_value`/linear-thread code paths (or leave the flag
  as a kill switch through M4; decide at flip time).

---

## 7. Risks / canaries (run each sub-stage)

| risk | canary | expectation |
|---|---|---|
| divergent footprint residual (U4) | `divergent.vpr` | 1 split today; may still need escape (cheap ladder / future Z3) |
| `gate_value` removal breaks field-write-in-if | `narrowing_*`, assignment corpus | green |
| `old`-heap off forked arms | `old_in_ensures` | green |
| wildcard through merge | wildcards corpus | wildcard stays `Leaf`, unchanged |
| dead-arm not dropped (fold too weak) | nested `unreachable!()` | 0 splits |
| flag-OFF drift | full `cargo test` at 4.1 | byte-identical to Stage 3 |

---

## 8. Checklist for the implementer

- [ ] 4.0 flag `SILVER_OXIDE_BLOCK_MERGE`, default OFF; A/B harness; baseline frozen.
- [ ] 4.1 `ChunkPerm` + smart ctors + `to_id`; migrate `Chunk`, `merge_chunks`,
      `heap_union`, `heap_subtract`, `find_chunk_consolidated`, `assume_location_axioms`,
      wildcard path. Gate: flag-OFF byte-identical. **Commit.**
- [ ] 4.2 lowering `h_in`-from-`Preds` + `Merge` emit + drop `gate_perm`/`gate_value` (flag);
      `merge_heaps` + `eval_heap_inst` Merge arm; `Heap::kinds`/`chunk_canon` helpers. Gate:
      `gen_enum_match 8` `NO_TIER4` green. **Commit.**
- [ ] 4.3 const-fold dead-edge detection in `select`; optional body-skip. Gate: nested
      `unreachable!()` 0 splits. **Commit.**
- [ ] 4.4 scale N=20/100; flip default ON; full suite + refreshed baselines. **Commit.**
- [ ] Update `PROGRESS.md` per sub-stage; update memory `project_block_vmir_impl_plan`.

## Status

Written 2026-07-27 (pre-implementation). Design settled in `30`/`50`; this is the code-level
lowering. Open at implementation time: exact wildcard-unguarded shape (§3.2), and whether
body-skip is needed for v1 (§5) — both resolved by measurement during 4.2/4.3.
