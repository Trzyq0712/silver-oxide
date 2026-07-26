# 10 — Block-structured VMIR

## Purpose

Define the IR that replaces CFG-linearization: preserve basic blocks + edges so the
verifier can run a per-block merge at real joins. Foundation `[20]`/`[30]`/`[50]` build on.

## Current understanding (decided / measured)

- Today: `method.rs` lowers the Viper CFG to a **linear** VMIR stream (`Method.insts:
  Vec<Inst>`); `reach.rs` computes each block's reach as a minimized DNF cube-set and
  phi-merges values with `ite`s (`build_entry_env`); `Inst.pc: PathConds` is a per-inst
  cube; `Val`/`HeapVal` are global positional SSA indices. Block-based VMIR = **stop short
  of the final linearization**, keep the CFG.
- `Inst.pc` **splits, does not vanish** (see §pc): the **control** part → block cube; the
  **expression** part (short-circuit `&&`/`||`/`==>`/ternary + separating-conj `Fact`,
  tagged `PcKind` in `sink.rs`) stays on obligation-bearing insts, finer than the block.

## Block model (decided 2026-07-26)

A block transforms an entry state into an exit state:
```
(env, h_in)  --body-->  (env', h_out)
```
- **env** = `Var → value` (many, name-resolved). **h_in/h_out** = the heap (one handle).
- Two phases: **join phase** builds the entry `(env, h_in)` from predecessors; **body
  phase** is straight-line SSA threading to `(env', h_out)`. All merge semantics live in
  the join phase; the body never merges.

### Join-source form — no terminators (decided)

The verifier is a **pred-driven merge machine**, not a jump machine. Store only **join
sources**; forward edges are their inverse. A block is:
```
block = ( cube, preds ∈ {0,1,2}, join_condition? , body_insts,  h_out )
```
Derived, never stored: successors (inverse of `preds`), branch/split & fork points (a
block that is `pred` of 2), the join condition (the literal where the two preds' cubes
diverge — stored for convenience), topo order (the pred-DAG), the **exit block** (nobody's
pred). `h_in` is derived from the pred declaration (entry → `entry_heap`; `from bbP` →
`bbP.h_out`; `join eC [P1,P2]` → `merge(P1.h_out, P2.h_out) on eC`).

- **Exactly 1 or 2 predecessors.** Joins are **binary**, described by the **value joined
  on** (the branch condition), not primarily by block ids. **n-way match = nested binary
  joins** mirroring the branch tree — each split has a matching downstream `join eC`. The
  structural merger collapses each binary step, so nesting does **not** rebuild the tower
  (the investigation's "nested worse than flat" was the *old additive* representation).
- **No `Switch`, no early `Return`, no `Unreachable` terminator** — Viper control flow is
  binary `if` + `goto` + `while`; results via out-params; `unreachable!()` is an
  `exhale false` **inst** (dead local), not a terminator.

### Values stay SSA (decided — do NOT drop SSA)

An SSA temp **is** an e-class; immutability is what value-numbering/hash-consing needs.
Mutable named vars would duplicate a `Var→e-class` layer SSA gives for free. So:
- **Intermediate/expression values: SSA temps** (`eN`), immutable, block-local.
- **Program variables (`var x`): standard SSA versioning.** Each assignment = a new temp;
  a join emits an **explicit phi temp**; post-join `x` = that phi temp. The `Var→temp`
  **env is translation-side** (the existing `env: Spur→Val` + `build_entry_env`, reused
  verbatim, now placed in the join phase).
- **Coupling that forced this:** *implicit* phis (join = header only) would require the
  body to reference **by name** (a verify-time phi value has no temp id) ⇒ drop SSA.
  *Explicit* phis keep SSA. We keep SSA; phis are explicit temps **confined to the join
  phase**. Cost: phi lines are listed (not implicit) — small, and the condition is not
  repeated (it's in the join header).

### pc — two levels

- **Control pc → block `cube`** (from `reach.rs`), shared by all the block's insts.
- **Expression pc → stays on the obligation inst** (`Inst.expr_pc`, the `Branch`/`Fact`
  part): short-circuit + separating-conj guards for `Div`/`Mod`, `acc` perm≥0, function-
  precondition WD, `assert` under `==>`. Value/heap **defs are unconditional** (the
  guarded emitters are already the only pc-carriers; plain defs are memoized/unguarded).

## Syntax (extends today's `eN`/`hN` display)

```
bbK <cube>:                         entry (0 preds); insts use <g> prefix only for expr-pc
bbK <cube> from bbP:                1 pred; h_in = bbP.h_out
bbK <cube> join eC [bbA, bbB]:      2 preds on eC (bbA ⇒ eC, bbB ⇒ !eC); h_in = merge on eC
  join:  eN: T := φ(eA, eB)         phase 1 — cross-block phi temps (condition from header)
  body:  eN: T := …                 phase 2 — straight-line SSA; hN := hM op …
```
`φ` on values = a phi temp (e-node); heap merge into `h_in` = the `[30]` structural
per-chunk merger. `@ h` = read-in-heap (deref/old/perm); `[h]` = obligation check-in heap.

### Worked: `var x`, both arms modify, use after join
```
method m(c: Bool) {
  bb0 <>:            body: e0: Int := havoc      # var x → x ↦ e0
  bb1 <c>  from bb0: body: e1: Int := 1          # x := 1 → x ↦ e1
  bb2 <!c> from bb0: body: e2: Int := 2          # x := 2 → x ↦ e2
  bb3 <> join c [bb1, bb2]:
    join: e3: Int := φ(e1, e2)                   # x ↦ e3 (condition c not repeated)
    body: assert e3 >= 1                         # "x" post-join = e3
}
```

### Worked: give-back over a binary join (heap h_in/h_out)
```
method m_add(a: Int) -> (r: Ref) {
  bb0 <>:                          # h_in = entry_heap
    body: e0: Int := a ; e1: Bool := e0 <i 0
  bb1 <e1>  from bb0:              # h_in = bb0.h_out
    body: h1 := h_in exhale acc(f(r),1/1) ; h2 := h1 inhale acc(f(r),1/1)   # h_out = h2
  bb2 <!e1> from bb0:
    body: h1 := h_in exhale acc(f(r),1/1) ; h2 := h1 inhale acc(f(r),1/1)   # h_out = h2
  bb3 <> join e1 [bb1, bb2]:       # h_in = merge(bb1.h_out, bb2.h_out) on e1 → perm(f(r)) 1/1
    body: h1 := h_in exhale acc(f(r),1/1) [h_in]                            # tier-4-free
}
```

### Worked: nested binary enum + dead block (deadness-agnostic)
```
  bb0 <>:            body: f0 := a==i 0 ; f1 := a==i 1 ; br is IMPLICIT (bbA0/bbC0 name bb0)
  bbA0 <f0>   from bb0:  … give-back … 
  bbC0 <!f0>  from bb0:  (splits to bbA1/bbDEAD)
  bbA1 <!f0,f1>  from bbC0: … give-back …
  bbDEAD <!f0,!f1> from bbC0: _ := h_in exhale false      # NOT a terminator; dead LOCAL
  bbJc <!f0> join f1 [bbA1, bbDEAD]:   # inner join; if bbDEAD's cube proves false →
      body: …                          #   ite folds to bbA1 (Route 1) at VERIFICATION time
  bbJ  <>    join f0 [bbA0, bbJc]:     # outer; ite(f0,1/1,1/1) → 1/1
      body: h1 := h_in exhale acc(f(r),1/1) [h_in]
```
**Deadness is verification-time, never static.** The IR lists both preds of every join; a
join is a full `ite` that collapses to the live arm **only when the verifier disproves a
pred's cube** (its `exhale false`). Topo order processes preds before the join → discovery-
before-use (loops break this — deferred). `reach` is **static/deadness-agnostic** (the
exhaustive cover `{f1,¬f1}` telescopes to the parent regardless); the collapse is the
verification-time `ite`-fold. This is exactly Route 1 (`[30]`).

## Execution modes

- **v1 (M1/M2): reuse ONE shared ground e-graph** (like today), walk blocks in topo order,
  pc-gate obligations. **No** per-block local, ghost archive, fork/merge → **no enode-id
  mapping**. The tier-4 killer still works: the perm structural-merge is over *explicit*
  terms + binary-join `ite`-collapse — needs neither forking nor id-mapping. So v1 can
  already collapse the exit perm tier-4-free. `join` merges the whole state (all env vars +
  heap; no liveness). See `[20]`/`[70]`.
- **Later (deferred): forking + isolation + remap** (`[20]`/`[30]` machinery) — the value
  e-node scaling story, slotting **into the join phase only** (bodies untouched).

## Loops / back-edges

DAG-shaped for M1. A back-edge is a `pred` that comes later in topo (latch precedes header
in data flow) → the header names a not-yet-processed pred → needs invariant + havoc.
Out of M1 scope; the block graph type must allow it (graph, not DAG). Forward terminators
would not have helped — same problem, no loss from join-source form.

## Rust mapping (2026-07-26)

**Reuse the whole value/heap/perm/inst vocabulary; add only the CFG layer.** Grounded in
the current types (`vmir::{Val, HeapVal, Perm, Inst, InstKind, PureInst, HeapInst,
PathConds}`).

**Already present — no new types needed:**
- `Val = Literal(Literal) | Temp(usize)` — SSA temps, unchanged. `HeapVal = Empty |
  Temp(usize)` — heap SSA temps, unchanged.
- **The explicit perm-AST is already `vmir::Perm`** = `Amount(Val) | Wildcard | Ite(Val,
  Box<Perm>, Box<Perm>)`. `[50]`'s "explicit perm term outside the e-graph" *exists*; the
  structural merger builds/collapses `Perm::Ite(cond, then, els)`. **No `Const·Sum·Scaled`
  type to invent** — `Perm` is it. (`Sum` is the aliasing Σ, which lives in the heap
  vec-per-location, not in `Perm`.)
- **Value phi = existing `PureInst::Ternary(cond, then, els)`** — `build_entry_env` already
  emits these. No phi node.
- `Inst = { pc: PathConds, heap: Option<HeapVal>, kind: InstKind }` — reused as-is; only
  the **meaning of `pc` narrows** to the expression-pc (`Branch`/`Fact`), empty on plain
  defs. Block cube moves out to `Block.cube`.

**The change: `Method` becomes a block graph.**
```rust
pub struct Method {
    pub name:   Spur,
    pub blocks: TiVec<BlockId, Block>,
    pub entry:  BlockId,          // the unique Entry block (derivable; stored for convenience)
}
pub struct BlockId(usize);        // #[derive(From, Into, …)], TiVec index

pub struct Block {
    pub cube:  PathConds,         // CONTROL cube (reused PathConds = conj of (Val, Polarity))
    pub preds: Preds,             // join-source form — CFG structure only
    pub join:  Vec<Inst>,         // join phase: phi `Ternary`s + a heap `Merge` (empty if <2 preds)
    pub body:  Vec<Inst>,         // body phase: straight-line SSA
    pub h_out: HeapVal,           // exit heap (cached: last heap produced, else h_in)
}
pub enum Preds {
    Entry,                        // 0 preds → h_in = entry_heap, env = params
    From(BlockId),                // 1 pred  → h_in = pred.h_out
    Join { cond: Val, then_: BlockId, els: BlockId },   // 2 preds → h_in = the join's Merge result
}
```
Only **one new inst variant** — the block-IR heap join:
```rust
// HeapInst::
Merge { cond: Val, then_h: HeapVal, els_h: HeapVal }   // structural per-chunk merge ([30])
```
The `join` phase is thus a tiny `Vec<Inst>`: value phis (`Ternary`) + one `Merge` producing
`h_in`. Everything is the existing `Inst` vocabulary — the verifier walks `join` then `body`
per block, exactly as it walks insts today.

**Derived, not stored:** successors, split/fork points, exit block, topo order (all from
`Preds`); `h_in` (from `Preds`: `entry_heap` / `pred.h_out` / the `Merge`); the join
condition is on `Preds::Join`. **No `Val::Var`** — SSA + translation-side `env: Spur→Val`
(the phis are `build_entry_env`'s output, placed in `join`).

**Deadness has no representation** — a dead block is just one whose `body` holds `exhale
false`; the verifier discovers it and the `Merge`/`Ternary` fold when a pred's cube is
disproven (verification-time, Route 1). `Preds`/`Block` never say "dead".

**v1:** one shared e-graph; `Merge` eval = the explicit-`Perm` structural per-chunk merge +
`Ternary` value merge; no fork/remap. Temps/heaps stay **global positional** (as today), so
no id-mapping.

## Open decisions

- `Method` params/returns: seed the entry env (translation-side) + appear as initial
  `Temp`s — pin the exact entry-heap source (`entry_heap` sentinel vs an entry inst).
- Keep the reach **DNF** (for `[30]` telescoping) vs the materialized reach val — keep DNF.
- Migrating the `Display`/walker (`inst.rs`'s `VmirDisplay`) to blocks (join/body sections,
  `<cube>` header, `from`/`join eC` pred line).

## Risks

- Over-refactor: M1 target is *no behaviour change* (still one graph, topo walk). Resist
  folding `[20]`/`[30]` semantics into M1.
- Loop representation must not be precluded by the block type.

## Depends on / feeds

Feeds everything. No upstream. Tightest coupling: `[50]` heap residency, `[30]` joins.

## Status

**sketched** (2026-07-26) — block model + join-source form + phases + SSA decision +
pc split + syntax + worked examples decided. Remaining: concrete Rust types + the perm-AST
shape, and the M1 no-op-refactor landing.
