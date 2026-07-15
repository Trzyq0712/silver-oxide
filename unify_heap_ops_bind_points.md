# Unifying heap ops via passed-in snapshot bind points

Status: design sketch, not implemented. Captures a design discussion. Distinguishes
settled observations (verified against `src/verify/declaration.rs` and `src/vmir/heap.rs`)
from open questions still to be settled.

## Core idea

Make the **snapshot ADT a passed-in input** to heap operations (a "bind point")
rather than a value the operation *mints as output*. Today an `Inhale` of a
self-framed resource mints a **fresh** snapshot `Val` (`snap_yield` in
`vmir/heap.rs`, `build_snapshot` in `declaration.rs:711`). If instead every
heap op receives the snapshot to bind against, three things fall out:

1. **Snapshots become ordinary bound logical variables with equality
   constraints** — egg-friendly (equality saturation over fresh vars is what the
   engine eats best), and inhale/exhale become symmetric (inhale binds `chunk :=
   proj(s)`, exhale binds `s := current chunks`).

2. **Fold/unfold collapse into shared-`s` exhale+inhale** (see below), removing
   the dedicated `HeapInst::Fold`/`Unfold` — at least for the *statement* form.

3. **The legality of inhale (and `Sub`) inside function/predicate bodies is
   recovered**, because the only thing those bodies were banned from —
   introducing fresh, observable values — no longer happens.

## The op family, unified

All of `Inhale`, `Exhale`, `Fold`, `Unfold`, `PureInst::Snap`, `HeapInst::FromSnap`
are the **same per-slot footprint loop** (`walk_footprint`, `declaration.rs:879`),
parameterized by:

| op | direction | slot value source | bool | perm amount |
|----|-----------|-------------------|------|-------------|
| `Inhale` | Produce (add) | `Fresh` | assume | concrete/given |
| `Exhale` | Consume (subtract) | `ReadHeap` | assert | concrete/given |
| `Fold` | Consume + add pred chunk after | `ReadHeap` | assert | concrete/given |
| `Unfold` | remove pred chunk first + Produce | `ProjectSnap(s)` | assume | concrete/given |
| `Snap` (fn precond) | Consume, non-consuming scratch | `ReadHeap` | assert | **wildcard** |
| `FromSnap` (fn body entry) | Produce onto held heap | `ProjectSnap(s)` | assume | irrelevant |

With snapshots passed in, the distinguishing axes are exactly: **direction**
(add/subtract), **value source** (fresh / read-heap / project-snapshot), and
**perm amount**. The snapshot itself is no longer an axis — it is the shared
binder threaded through.

## Fold/unfold as shared-`s` exhale+inhale (verified)

Confirmed against the evaluator:

- **Fold** (`declaration.rs:719`): `walk_footprint` `Consume` — subtract each
  footprint slot (scaled by the multiplier) from the held heap, read slot values
  from that heap, **assert** the body bool; then `heap_union` a predicate chunk
  at `pred_addr` valued `cons(consumed values)`. Chunk added **after**.
- **Unfold** (`eval_unfold`, `declaration.rs:1015`): recover snapshot `s` from
  the held predicate chunk, `heap_subtract` that chunk **first**, then
  `walk_footprint` `Produce` — reproduce each slot valued `unwrap(proj_i(s))`,
  **assume** the body bool.

This is precisely `exhale`/`inhale` machinery. So:

- **fold P(x)** = `exhale body` yielding `s` (s = body chunk values) **+**
  `inhale P(x)` with the **same** `s` → P's snapshot bound to `cons(body)`.
- **unfold P(x)** = `exhale P(x)` binding `s` (s = P's snapshot) **+** `inhale
  body` with the **same** `s` → body chunks = `proj_i(s)`.

The shared `s` is the tie between predicate-snapshot and body-snapshot. This is
exactly the binding the *old* attempt lost: when the snapshot was a minted
**output**, `inhale P` produced a **fresh arbitrary** snapshot and nothing forced
`snap(P) = cons(body)` — which is why fold/unfold were kept first-class
("desugaring into inhale/exhale proved too hard to do soundly", per CLAUDE.md).
Snapshot-as-**input** removes exactly that gap. The snapshot ADT (`cons`/`proj`
round-trip) remains, now as the *type* of `s`; the binding is emergent.

The only extra fold/unfold carry over a plain inhale/exhale pair is the
**predicate-chunk bracketing** (add-after for fold, remove-before for unfold),
which the shared-`s` pair already expresses.

## The well-definedness principle (sharpened)

Functions and predicates must be **deterministic** (referentially transparent in
params + heap + snapshot). The real ban is therefore **not** "no inhale" or "no
`Sub`" — it is:

> **Legal iff every fresh value is either (a) bound to an in-scope term, or
> (b) provably unobserved by the body's result/snapshot.**

- Snapshots → case (a): bind points supply the binder, so inhale no longer mints
  a fresh observable value. **Inhale becomes legal in function/predicate bodies.**
- Wildcard perm amounts → case (b): the fresh symbolic amount `w` is never
  observed by the returned value (the chunk value read is amount-agnostic;
  `0 < w < held` only constrains). This is why wildcard already lives inside
  function bodies.

`Sub`'s original ban was **ad-hoc** — it introduces no fresh value and was simply
never needed (confirmed with the user). A resource cannot end up holding negative
permission because the resource's own well-definedness check rejects it, so
monotonicity is self-enforcing and independent of the `Sub` ban. `Sub` can
therefore be permitted in function/predicate bodies under the same principle,
though fold/unfold desugaring does **not** need it (the subtracting side is a
legal `exhale`).

## Wildcard (corrected model)

Wildcard is **not** a duplicable / non-linear permission class. It is a **fresh
symbolic real `0 < w < 1`, upper-bounded by the currently-held permission** at the
point of use, so that exhale is always safe (caller keeps `held − w > 0`) and
inhale never reaches `1/1`. It is still linear consumption; the "idempotent from
outside" appearance is emergent from the fresh-bounded amount plus the fact that
the read value does not depend on the amount. (Silicon: functions share the method
heap, with permission amounts rewritten to `0`/wildcard mid-translation.)

Design impact: in silver-oxide, resource **framing** is a syntactic `HashSet`
presence check, while fractional **amounts** live in the e-graph. Wildcard needs
its bound `0 < w < perm(held)` emitted as an e-graph assumption at the `Snap` /
precondition site (the held amount is the symbolic chunk-sum the e-graph already
has).

## Side condition: fold/unfold multiplier must be `> 0` (fix regardless)

Currently **missing**. `Inhale` gates its bool-assume by `0 < scale`
(`declaration.rs:682`), but `Fold` (`:719`) and `Unfold` (`:1015`) take the
multiplier as `scale` with **no positivity assertion**; the per-slot `present`
discriminant uses the *unscaled* recipe perm (`:947`), so the multiplier is never
checked. Consequences:

- `fold P(x, w)` with `w < 0` → `heap_subtract` of a negative-scaled chunk =
  **adds** permission = fabrication → **unsound**.
- `w = 0` → asserts the predicate body for free.

Fold/unfold must **assert `perm > 0`** (a hard assert, since they consume — unlike
inhale's assume-guard). Worth fixing independently of the unification.

## Recommended sequencing

1. **Snapshot-as-input bound var** first — decoupled from the perm question,
   independently improves egg encoding, and is the enabler for everything else.
2. Prototype **unfold-statement** desugar to shared-`s` exhale+inhale on a
   *non-recursive* predicate (`cases/`), and diff the resulting e-graph merges
   against the first-class `Unfold` path. If identical, extend to
   recursive-but-explicit folds/unfolds.
3. Add the **`perm > 0`** side condition to fold/unfold (can land now).
4. Model **wildcard** as a fresh symbolic real with the `0 < w < perm(held)`
   e-graph assumption; `Snap` then becomes `exhale`-at-wildcard and `FromSnap`
   the reconstruction outlier.

## Worked example: nested predicate unfold/fold via bind points

```viper
predicate List(x: Ref) {
  acc(x.val) && acc(x.next) &&
  (x.next != null ==> acc(List(x.next)))
}

method example(x: Ref)
  requires acc(List(x), 1/1)
{
  unfold List(x)
  if (x.next != null) { unfold List(x.next) }
}
```

Unfold desugars to **`Combine`-sub (remove chunk, yielding `Option<Snap>`) →
`unwrap` (own explicit obligation) → `Inhale` bound to that snap** — not a
separate `deref` + `Combine`-sub + a hand-unrolled per-field `Combine`+`Assign`
chain. The body's own guarded structure (the `x.next != null ==>` conjunct) is
*internal* to `List`'s cached `ResourceCertificate`; the desugaring replays it,
it doesn't re-derive it:

```
<>  a1 := List@addr(x)
<>  h1, s0? := h0 - acc(a1, 1/1)         // Combine, Sub — yields Option<Snap(List)>,
                                          //   Some iff perm(h0,a1) > 0, else None
<>  s0 := unwrap(s0?)                     // Pure/Unwrap — explicit obligation
                                          //   is_some(s0?); NOT free from unwrap's
                                          //   own semantics (pure ADT destructor,
                                          //   doesn't "get stuck" — the e-graph would
                                          //   happily treat unwrap(None) as an arbitrary
                                          //   uninterpreted term otherwise, unsound).
                                          //   Discharged here by `requires acc(List(x),1/1)`.
<>  h2 := h1 inhale List(x) 1/1 @s0      // Inhale, bound to s0 (not fresh) — replays
                                          //   List's cert body, slots sourced from
                                          //   proj_val(s0)/proj_next(s0)/proj_tail(s0)

<>  a2 := next@addr(x)
<>  e1 := deref(h2, a2)                  // legal now — h2 holds it, produced above
<>  a3 := List@addr(e1)
<e1 != null>  h3, s1? := h2 - acc(a3, 1/1)
<e1 != null>  s1 := unwrap(s1?)          // obligation only under e1 — sound, guarded
<e1 != null>  h4 := h3 inhale List(e1) 1/1 @s1  // s1 should land in same e-class as proj_tail(s0)
```

Fold is the mirror: `Exhale` (self-framed, same `Option<Snap>` yield —
consumes the fields, reads real values, no fresh needed on that side) then
`Combine`-add the predicate chunk bound to that snap, not fresh:

```
<>  h1, s0? := h0 exhale List(x) 1/1     // Exhale — consumes val/next/(cond) chunks,
                                          //   asserts body bool, yields Option<Snap>
<>  s0 := unwrap(s0?)                     // same explicit obligation as above
<>  h2 := h1 + acc(a1, 1/1)              // Combine, Add
<>  h2 := assign(h2, a1, s0)             // bind chunk value to s0 — this is the equation
                                          //   `snap(List(x)) = cons(body)` that first-class
                                          //   Fold/Unfold need but minted-fresh Inhale loses
```

**Why the exhale/inhale asymmetry is principled, not arbitrary.** `Exhale` is
inherently read-shaped — the heap already holds a determinate value, exhale's
job is to surface it; giving it an input snap would only be a redundant
equality check. `Inhale` is inherently write-shaped — it has no value by
default, so its value-source is a genuine parameter: `Fresh` (havoc, legal
only in method bodies / unobserved cases like wildcard) or `Bound(v)` (case
(a) legality, legal everywhere including fn/pred bodies). Fold/unfold always
land in the `Bound` case because the value is always sitting right there from
the paired exhale.

**The same axis applies one level down, to `Combine`.** `Combine(Add)` (a
single-slot perm gain, e.g. plain `inhale acc(x.f)`) is the same produce event
as `Inhale`, just at slot granularity — it should carry the same
`Fresh | Bound(v)` param instead of being followed by a separate `Assign`.
This is what lets the per-slot loop above be *literally* `Combine(Add) @s`
rather than a hand-rolled `Combine`+`Assign` pair — `Fold`/`Unfold`'s
`walk_footprint` reduces to a loop over one primitive, not two. `Combine(Sub)`
should symmetrically read+yield the consumed value, same as `Exhale`, for the
same reason. **`Assign` (standalone, no perm change — plain `x.f := v` on an
already-held loc) stays genuinely separate**: it's not a produce event at all
(no perm change, pre-existing slot, caller-supplied value by construction,
never fresh) — it isn't on this axis.

Unified table, sharpened:

| op | shape | value source |
|----|-------|--------------|
| `Combine(Add)` / `Inhale` | produce | `Fresh \| Bound(v)` |
| `Combine(Sub)` / `Exhale` | consume | always read + yield |
| `Assign` | overwrite, no perm change | caller value, always bound (orthogonal axis) |

## Open questions (not settled)

- **The yielded snap must be `Option<Snap>`, not `Snap`, and this is a
  pre-existing gap, not new.** `inst_obligations` (`declaration.rs:2921`)
  checks only `perm(amount) >= 0` for `Combine`/`Inhale`/`Exhale` — never
  strict `> 0`. So `exhale List(x) 0/1` is legal today, and `Exhale`'s
  existing `snap_yield` (`heap.rs:82`) hands back a snap `Val` regardless —
  nothing backs it when perm is 0, since nothing was ever required to be
  held. A hard `perm > 0` obligation at the yielding op would over-constrain
  (a zero-perm exhale/`Combine(Sub)` is a legitimate vacuous no-op in Silver,
  e.g. `unfold acc(P(x), 0)`; rejecting it outright is wrong). Correct fix:
  the yield type is `Option<Snap>` — `Some(s)` iff `perm > 0` else `None`.
  **Some check must exist before the value is consumed — not inherently
  "unsound" otherwise, just underspecified.** `unwrap` is a pure ADT
  destructor and doesn't self-enforce anything (`unwrap(None)` doesn't "get
  stuck," the e-graph would just treat it as an arbitrary term) — so *some*
  mechanism has to discharge `is_some`. An explicit `Assert(is_some(opt))` in
  the IR (reusing the existing `Assert` primitive, not a bespoke
  `inst_obligations` match arm) is one valid way to provide it.
- **Performance constraint: that check must NOT become a genuine e-graph
  proof goal, or the desugar regresses perf vs. today's `Unfold`.** Checked
  `eval_unfold` (`declaration.rs:1121-1124`): today's sufficiency check is a
  **direct structural lookup** on the definite-chunk map —
  `base_h.entries().find_map(...).ok_or(InsufficientPermission)`, congruence
  via `ctx.egraph.find` (O(1) union-find), no saturation triggered. If
  `Combine(Sub)`'s `Option` yield is unwrapped via a real e-graph `Assert`
  goal (the same machinery as e.g. `f#ensures` guard facts), that's strictly
  more expensive — a proof search where today there's a hashmap lookup. Fix:
  keep `Option<Snap>` as the *semantic* description, but evaluate
  `Combine(Sub)` (+ its unwrap) via the same structural lookup path
  `eval_unfold` already uses — no separate proof-search goal, so the
  desugared `unfold` costs the same as the first-class one. IR gets the
  cleaner compositional shape; the evaluator, not the solver, absorbs the
  check. Confirms the doc's "diff e-graph merges against first-class `Unfold`"
  sequencing step — that diff should show zero extra proof obligations, not
  just "same final merges."
- **Definitional (automatic) unfold must stay lazy.** Explicit fold/unfold
  *statements* are finite and safe to desugar, even for recursive predicates.
  But function definitional unfolding is a lazy on-demand rewrite (memory: "fn
  certs = lazy unfold rules") — eagerly desugaring it would diverge on recursive
  predicates. The desugaring above is for the **statement** form only; confirm
  the original "too hard to do soundly" blocker was purely the snapshot binding
  and not also laziness before removing `HeapInst::Unfold` outright.
- **Wildcard under multiplication inside a predicate/unfold.** The composition
  `w * q` (wildcard amount scaled by an inner body fraction) is a known murky
  corner in Viper/Silicon; the exact rule (per-chunk vs. exhale-total bound,
  freshness of the product) needs pinning against the Silicon source before
  building on it.
- **`inhale P` assuming P's bool.** For a concrete predicate, P's bool is derived
  from the body; assuming it on the inhale side of a fold is sound only because
  the paired `exhale body` just asserted it. Fine by construction, but the
  desugaring must always keep the body-exhale in front of the predicate-inhale.
