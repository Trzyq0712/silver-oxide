# Snapshots, Fold/Unfold, and Function Purification — Design Direction

Status: design notes (Phase 2–3). Captures a design conversation; not yet implemented.
This is the intended direction for predicate bodies, fold/unfold, and heap-dependent
function purification in the egg backend.

## Decisions (settled)

1. **Fold/unfold are dedicated structural primitives; methods stay desugared to
   inhale/exhale (`Combine{Resource}`).** Principle = **reducibility**: desugar what
   reduces, keep irreducible as a primitive.
   - A resource call produces an **opaque delta with fresh values** (cert verified
     against an empty ctx). That is *correct* for a method call (callee changes the heap
     arbitrarily) → `Combine{Resource}` (assert/assume the bool). It is also the *more*
     primitive form, so desugaring methods aligns with the dumb-IR ethos — keep it.
   - Fold/unfold are a **ghost, value-preserving identity**: the predicate snapshot must
     equal the make_snap of the *current* fields and unfold must return exactly those.
     A resource call cannot carry value-preservation (its delta values are fresh by
     construction); forcing it would require the `make_snap` + `assume` crutch (soundness
     amplifier, fold↔unfold as axiom not congruence, extra `Deref`/uninterpreted nodes).
     So fold/unfold are **irreducible** → dedicated `HeapInst::Fold/Unfold`, structural,
     fold↔unfold round-trips by `proj(cons)=>arg` congruence (no assume).
   - `Combine` = primitive for **opaque** resources; `Fold/Unfold` = primitive for
     **value-preserving** ghost moves; `unfolding … in` reuses `Unfold`. The asymmetry is
     principled (different semantics), not an accident — do NOT unify for symmetry's sake.
   - Cost accepted: two backend code paths (`Combine` graft/scale/union-sub/assume-assert
     vs `Fold/Unfold` structural cons/proj), sharing `heap_union`/`heap_subtract`/graft.

2. **Snapshotted resources must have `requires == None`; fold/unfold/snapshotting are
   disallowed on resources with a precondition resource.**
   - Forced reason: a snapshot captures only the **footprint**. A body that reads a ctx
     heap (`Temp(0)` = its precondition resource's delta) has reads that are NOT in the
     snapshot → cannot reconstruct `H(s)` → unsound. So snapshotted bodies must read only
     their own footprint, i.e. `requires == None`.
   - Naturally satisfied: the precond-resource mechanism is for **two-state** resources
     (`m@ensures` has `requires: Some(m@requires)` — postconditions relate pre/post). The
     things snapshotted are **one-state**: predicates (folded) and `f@requires` (purified),
     both `requires == None` by construction. `old` is illegal in predicates.
   - Disjoint mechanisms: a resource is **either** opaque-with-a-ctx (two-state contracts,
     handled by `Combine`, never snapshotted) **or** snapshotted-and-self-contained
     (predicates / fn preconditions, `requires == None`). Never both.
   - Enforce: `Fold`/`Unfold` + snapshot-construction + function purification assert
     `requires == None`, with a clear error. Never fires on well-formed frontend output.

   | kind | `requires` | handling | snapshotted? |
   |------|-----------|----------|--------------|
   | predicate `P` | `None` (1-state) | `Fold`/`Unfold` (structural) | yes |
   | `f@requires` | `None` (1-state) | reconstruct `H(s)` (purify) | yes |
   | `m@requires`/`m@ensures` | ensures `Some` (2-state) | `Combine` (inhale/exhale, opaque) | no |

## Core model

- Predicates, method contracts, and function preconditions are all **resources**
  (a guarded inst stream producing `(heap_delta, bool)`). The resource's `delta` is
  its **footprint**.
- A symbolic heap `Chunk` already carries a `value: egg::Id`. The **snapshot of a
  resource is exactly the tuple of those chunk values** — no separate `make_snap`
  uninterpreted function is needed.
- A predicate instance held in the heap is a chunk at `P@addr(args)` whose `value`
  is the predicate's snapshot (an ADT value).

## Snapshots stay opaque in VMIR; structure materialized lazily at verification

The snapshot **type stays opaque in VMIR** — exactly as today (`P@snap` is an opaque
`Domain`; the snapshot value is `Deref(h, P@addr(args))`). The structured form below is
a **verification-time refinement** of that opaque type, derived on demand. Rationale:
VMIR doesn't commit to a snapshot encoding (Opt-vs-flat, constructor-vs-accessor, member
typing all become verification concerns); there is one source of truth (the body acc
sequence) with no separately-maintained decl to drift; nothing is lost (structure is
deterministically recoverable from the body).

Two **views of the footprint**, both kept:
- **Premerged (layout) view** = the resource body's acc sequence in program order (the
  ordered `Combine{Loc/Resource}` inst stream, each carrying its addr-expr + member
  type). This *is* the snapshot structure. Already in VMIR — nothing new to store.
- **Merged (accounting) view** = the post-saturation `delta` heap (chunks keyed by
  congruent address, perms summed). Used only for sufficiency / value-agreement /
  scaling.

When structure materializes:
- **Pure e-graph reasoning** (fold/unfold, function body eval): `cons`/`proj`/`unwrap`
  are `Symbolic` nodes keyed by `(resource, arity, index)`; **no declared ADT needed** —
  congruence + `proj(cons)=>arg` suffices. Ordinary verification never materializes a type.
- **VMIR-pure emission** (purified, heap-free form, produced by the *verifier* — e.g. for
  a Z3 handoff): materialize the explicit `Adt` decl here, because a downstream consumer
  needs a real type. Lazy / on-demand: you only pay for the snapshot types you emit.

Pipeline: translator → heap-dependent VMIR (opaque snapshots) → verifier →
(optional) VMIR-pure with materialized snapshot ADTs. The opaque `P@snap` Domain is
**refined** into the structured `Adt` at that boundary. Constructor identity must be keyed
by resource `MemberId` (stable across fold/unfold and call-site grafts; a predicate's
snapshot used as a member of a function's snapshot references the same `R@snap` identity).

## Snapshot ADT (the materialized structure)

- `R@snap = cons(member_0, …, member_n)` — **one member per syntactic `acc`** in the
  resource body, in **program (source) order**.
- Member types: field acc → `Opt[fieldT]`; predicate acc → `Opt[Q@snap]` (the nested
  predicate's snapshot, read opaquely — never recursively reconstructed).
- **`Opt[T]` is mandatory and must be a real lifted/option type.** A bare `T#empty`
  sentinel is UNSOUND: `Int#empty` would equal some integer in the model, so a held
  field hitting the sentinel becomes indistinguishable from "absent" → congruence
  collapses. Use `Some/None`.

### Membership is binary (perm > 0), amount irrelevant to the snapshot
```
member_k = (perm_k > 0) ? Some(value_at(addr_k)) : None
```
- The fractional **amount** never enters the snapshot — only positivity. Amount lives
  solely in the accounting path (sufficiency, framing, `Combine{perm}` scaling).
- Literal positive perm (`write`, `1/2`) → `perm>0` const-folds `true` → `Some`,
  wrapper peels away.
- Conditional acc (`b ==> acc(...)`) → perm gated to `b ? p : 0` → `perm>0` reduces
  to `b`. The discriminant *is* the branch condition, derived, not stored.
- Symbolic perm param (only `p ≥ 0` known) → `perm>0` is a genuine symbolic boolean.
- Consequence: `p(…,1/2)` and `p(…,3/4)` folded from the same fields produce
  identical members (both `Some(v)`); only the instances (addresses) differ.

### Layout is program-shape, NOT merged-heap shape
The footprint layout = ordered `[(addr_expr, perm, type)]`, sourced from the resource
**body instruction stream** (one `Combine{Loc/Resource}` per syntactic acc, in order).

Do **not** derive the snapshot from the post-saturation merged `delta` heap:
- it's `im::HashMap`-iteration ordered (nondeterministic),
- merges collapse aliased locations, so the member count would depend on what the
  e-graph *proved* (e.g. `x==y`) → perm-provability-dependent ADT arity → impossible
  to generate consistently.
The merged heap is used only as the **value source / perm accounting**. Aliased slots
(`acc(x.f)&&acc(y.f)`, `x==y`) keep two slots; both read the same agreed chunk value.

(Layout comes from the **body inst stream** (already program-ordered + typed), NOT from
the merged `delta` heap. So the merged delta needs no rework — it stays the accounting
view; the body is the layout view.)

## Fold / Unfold as VMIR heap primitives

```rust
enum HeapInst {
    Combine { base, sign, target, perm },     // method contracts (opaque delta + assume/assert)
    Fold   { base: HeapVal, call: ResourceCall, perm: Val },
    Unfold { base: HeapVal, call: ResourceCall, perm: Val },
    Assign(..),
}
```

Distinct from `Combine{Resource}` (method call: opaque whole-delta, fresh values,
assume/assert the bool). Fold/unfold crack the body open and **move the actual chunk
value symbolics**, build/project the snapshot ADT, and need **no snapshot `assume`**.

**Verifier — Fold** (footprint from cert, instantiated via graft/transplant):
```
h = base
members = []
for (addr, perm_k, type_k) in footprint:    // program order; addrs may deref earlier reads
    need = perm * perm_k
    c = h.chunk(addr)?
    prove h.perm(addr) >= need under pc      // sufficiency
    members.push( (perm_k>0) ? Some(c.value) : None )   // value straight from heap
    h = h.sub_perm(addr, need)
prove bool_id under pc                        // assert the body's pure facts
snap = cons(members...)
h = h.add_chunk(P@addr(args), perm, value = snap)   // construct chunk value = snap (no assume)
```

**Verifier — Unfold** (inverse): prove `perm` at `P@addr(args)`, read its value `s`,
subtract it, and for each slot add a chunk with value `unwrap(proj_k(s))`; `assume`
the bool. `proj_k(cons(..)) → member_k` makes fold→unfold a definitional round-trip
(pure e-graph, no SMT). `s` may be opaque (came from an inhaled predicate) — then
`proj_k(s)` stays uninterpreted, which is correct.

### Why not "ResourceCall + make_snap + assume"
The earlier sketch used `e := make_snap(...)` (uninterpreted fn over `Deref`s) then
`assume pred_value == e`. Problems removed by constructing the chunk value directly:
- the `assume snap == make_snap` is a **soundness amplifier**: if perm accounting ever
  over-grants, the assume silently derives `false` → method "verifies" everything. The
  identity is safe in Viper (fold/unfold preserve field values; permission discipline —
  writes need full perm, folding locks a fraction — prevents conflicting re-folds), but
  it has no independent safety margin. Constructing `value = snap` removes the extra
  assume site. Fold↔unfold becomes congruence (`proj∘cons`), not an axiom.

Needed backend rewrites: `proj_k(cons …) => arg_k`, `unwrap(Some ?x) => ?x`.

## Heap-dependent function purification

Replace a function's heap argument with the **snapshot of its precondition**.
Resolution of field/predicate reads to snapshot members is **verification-time
congruence**, NOT a translation-time rewrite.

### Why not translation-time
`acc((b ? x : y).f)`: footprint addr is `f@addr(ite(b,x,y))`. A body read `x.f` equals
that slot **only under `b`** (ite-true). Matching needs pc + congruence, available only
at verify time. Also `(b?x:y).f` vs `b ? x.f : y.f` are equal by ite-distribution but
not syntactically. So a static `read ↦ proj_k` map is impossible in general.

### What translation emits (NO purification here)
For `function f(p): T requires P { body }`:
1. `f@requires` resource (footprint + precond bool).
2. opaque `f@requires@snap` type (a `Domain`, as predicates do today) — NOT a structured
   ADT. Its `cons`/member structure is materialized lazily at verification (above).
3. `Function` decl with a **heap-dependent body inst stream** reading the precond heap
   `Temp(0)`: field read → `Deref(Temp(0), addr)`; `unfolding P in e` → `HeapInst::Unfold`
   producing `h'`, then `e` reads `h'`; recursive/other calls carry the appropriate heap
   (`f(args)[h]`); result is a single `Val`.

Heap-dependent VMIR (translator output) thus contains: `Deref/Perm/FunctionCall/Binary/
Ternary/Lit`, `Unfold`, path conditions, **opaque** snapshot types, and functions/calls
that still **carry a heap**. It does NOT contain `cons/proj/unwrap`, `H(s)`, or
snapshot-as-argument. Those appear only at verification, and the structured snapshot
`Adt` decls only in emitted **VMIR-pure** (verifier output).

### What verification does
`verify_function(f)` (once, like `verify_resource`):
1. footprint from `f@requires` cert.
2. fresh params + fresh snapshot `s : f@requires@snap`.
3. reconstruct `H(s) = { addr_k ↦ Chunk(perm_k, unwrap(proj_k(s))) }`.
4. bind `Temp(0) := H(s)`, eval the body; each `Deref(H(s), a)` **congruence-resolves**
   to the footprint chunk whose value is `unwrap(proj_k(s))` — **this is where the
   heap-access→snapshot-field mapping is learned**, per deref, robust to ite/aliasing.
5. record the **defining equation** `f(params, s) == E` (E = body result) in the cert.

At a call site `f(a)[h]`: assert footprint framed in `h`; build
`s_a = snapshot(h, footprint)` (`cons` over `h`'s chunk values at footprint addresses,
no perm removed — functions frame, don't consume); emit pure node `f(a, s_a)`; graft
the defining equation (gated). The verifier narrows the heap to a snapshot at the call
boundary and reconstructs a heap from the snapshot inside the body.

### Shared op (factor out)
`snapshot(heap, footprint) -> snap_id` — read chunk values + `cons`, no mutation.
Used by: fold (then subtract), function call (assert framing, no subtract), and as the
predicate chunk value.

### Recursion gating (the real engineering risk)
Graft the defining equation only as deep as the snapshot is **concretely known**
(`cons`-rooted from a fold chain). On an **opaque** snapshot, stop — keep `f(a, s_a)`
uninterpreted and reason via its postcondition axioms. Otherwise the recursive
equation diverges in saturation (e.g. `len` over an abstract list: `cons(proj_k(s))`
on opaque `s` descends into ever-deeper projection terms). This is the
"quantifier-instantiation-in-egg" knob.

## `unfolding` has two flavors
- statement `unfold` / `fold` (method body): heap transform — the `HeapInst::Fold/Unfold`
  primitives.
- expression `unfolding … in` (function/assertion body): also lowers to `Unfold` over a
  local heap value; pure (no persistent heap mutation). Same footprint layout drives both.

## Load-bearing invariant: self-framing
Snapshot determinism (congruence), fold/unfold round-trips, and function purification
all require every read to be framed by the resource's own footprint. **Self-framing
must become a first-class CHECKED property** of every resource (predicate body, function
precondition, contract), not an assumed one — it is what guarantees every body read
resolves in `H(s)`.

## Open problems / not yet handled
- Quantified permissions (`forall i :: acc(a[i].f)`): one syntactic acc, unbounded
  chunks → "member per acc" breaks (member would be a map/seq). Phase 4.
- Constructor-ADT (`cons`, injective → powers congruence) vs uninterpreted accessors
  (handles recursion/QP naturally, one-directional). Leaning constructor; may need both.
- Wildcard perm `acc(P(…), *)` × fractional fold interplay underspecified.
- Predicate Perm *argument* vs fold *fraction* must compose without double-counting.
- Cert `delta` must be reworked to be order-stable + typed per slot before any of this.
