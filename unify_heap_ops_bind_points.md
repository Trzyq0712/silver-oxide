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

## Open questions (not settled)

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
