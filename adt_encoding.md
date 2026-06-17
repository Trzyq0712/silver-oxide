# ADT Encoding in the egg backend — Design Decisions

Status: decided (Phase 2/3). Companion to `snapshots_fold_unfold_function_purification.md`
(snapshot ADTs use the *same* machinery as user ADTs). Implementation tracked on branch
`adt-support` / plan `i-would-like-to-joyful-globe.md`.

## Decision: approach 1 — FuncApp + metadata + custom reductions

Constructors and destructors are ordinary `Symbolic::FuncApp` (constructors already lower
this way). An ADT-metadata side table (like `func_ret_types`) classifies member ids:
- `ctor_id → (adt, tag_index, arity)`
- `dtor_id → (ctor, field_index)`
- `tag_fn_id → adt`

Reductions are a **custom `Searcher`+`Applier`** (pattern after `UnionEqArgs`), NOT `rewrite!`
strings — `from_op` can't parse `FuncApp` (`fnN`), so FuncApp isn't string-matchable.
- **Projection**: `FuncApp(d,[x])`, `d`→`(c,i)`; if `x`'s e-class has `FuncApp(c, args)`,
  union with `args[i]`. (= `dtor(ctor(..)) ⇒ field`.)

Rejected alternatives: dedicated `Symbolic::Ctor/Dtor/Is` variants (more invasive, touches
every match site); ADT-aware analysis (approach 3, deferred — see disequality below); Z3
datatypes (fallback only).

## Decision: discriminators via a per-ADT `@tag`

Do NOT emit per-variant `is_C` functions or O(variants²) discriminator rules. Instead:
- one `Adt@tag` function per ADT (`→ Int`);
- translation desugars `x.isC` to `Binary(Eq, Adt@tag(x), index_C)`;
- reduction `Adt@tag(ctor_C(..)) ⇒ index_C` (a tag-rule per ctor); the `==` then folds via
  existing `ConstFold`.

Verifies discriminators on known constructors with no disequality machinery, e.g.
`adt MyAdt { one() two() }  var x := one(); assert !x.istwo`:
`x.istwo` = `tag(one()) == 1` → `0 == 1` → `false` (ConstFold) → `!false` → `true`.

**Bonus — constructor distinctness for free.** If a program ever forces `one() == two()`,
congruence merges `tag(one())` and `tag(two())`, i.e. int literals `0` and `1` collide in one
e-class → `ConstFold::merge` conflict (today a *panic*; that site is the contradiction hook).
So distinctness within an ADT falls out via existing constfold, without disequality edges or
a fork. (Injectivity still separate.)

## Deferred: disequality / full datatype theory

egg stores equalities, not disequalities. Distinctness for an **opaque** scrutinee (reason
from `assume x.isone` to `!x.istwo`) and injectivity (`Cons(a)==Cons(b) ⇒ a==b`) need more
than reductions. Two directions (deferred):
1. **No-fork encoding**: assert `A ≠ B` as `union(Eq(A,B), false)` + reflexivity
   `(== ?x ?x) => true`; if `A`,`B` merge, `Eq` canonicalizes to `Eq(C,C)` → reflexivity
   gives `true`, colliding with the `false` → `ConstFold::merge` contradiction. The tag trick
   above is a special case (int-literal collision).
2. **Fork egg** for native ≠ edges (supervisor's suggestion): lighter representation, ≠
   detected directly at `union`. More maintenance.
ADT distinctness/injectivity facts are **unconditional** (datatype theory) → sound to add to
the per-unit e-graph globally. The path-dependence trap only bites *user-level* `assume a != b`
(would need pc-gating) — the genuinely harder, separate problem. Either way, the
`ConstFold::merge` conflict site must become a "assumptions infeasible → goal discharged"
signal instead of a panic; mind that a collision means the **whole verification unit's**
unconditional assumptions are inconsistent, not one path.

## Derived accessors must not be emitted as decls (directive)

The synthesized accessors — `field@addr`/`pred@addr`, `P@snap`, the snapshot
`P@snap@cons`/`proj_i`, and `@tag` — have a **clearly defined structure trivially
implied from the resource/predicate/ADT definition**. They should **not** be
emitted as standalone `Declaration`s (the resource definition is the source of
truth); materialize them only **behind a flag, for inspection**. This matches
CLAUDE.md's "resource@addr/@snap not emitted explicitly" principle, which the
current code violates (`declare_predicate_accessors`, `declare_field_accessor`,
the ADT pre-phase all emit them today).

`@addr` is uninterpreted (no definition); `@snap`/cons/proj's "definition" is the
`proj_i(cons(..)) ⇒ arg_i` reduction (a verifier rule). So they are genuinely
derived — any decls are only id-allocation for e-graph `FuncApp` nodes.

### Naming convention: `@`-suffixes are reserved for generated members
A `@`-suffix (`@addr`, `@snap`, `@snap@cons`, `@snap@proj_i`, `@tag`, …) marks a
**generated implicit member** that sits alongside a user-named resource. A member
that *is* the canonical VMIR meaning of a user name carries the **bare user name**,
no suffix. Concretely: a **field**'s address function is emitted under the field's
own name (e.g. `f`, not `f@addr`) — a field has exactly one VMIR meaning, its
`Ref -> Addr<T>` accessor, so the bare name is canonical. A **predicate** keeps its
bare name for the resource itself and reserves `P@addr`/`P@snap`/… for the generated
helpers that accompany it. (Implemented in `declare_field_accessor`,
`src/translate/mod.rs`.)

Realizations: (A, minimal) keep decl slots but mark synthetic + hide from
`Display` unless a flag is set; (B) decouple accessor ids from decl indices
(today `MemberId` == `decls` index). To be implemented; recorded as direction.

## Type-parametric ADTs (deferred — design only)
Monomorphize at the egg boundary: `(generic_id, [Type]) → mono MemberId`, lazily at use sites,
so `Some@Int` / `Some@Bool` are distinct `FuncApp`s. Requires the typed `Domain(Ident,
Vec<Type>)` instantiation to survive to the boundary (VMIR strips it today).
