# VMIR and Verifier Architecture

## 1. Context and Motivation
The Viper→VMIR translation used to eagerly emit synthetic members — `@tag`
functions, `@dtor` accessors, per-type `Option[T]` ADTs and their
constructors — and the verifier reasoned over those declaration ids directly.
That coupled three concerns that should be separate: the IR's surface syntax,
the set of declarations, and the verifier's e-graph naming.

The redesign separates them:

1. **VMIR** is a pure, human-readable semantic AST. ADT operations are explicit
   nodes; no synthetic `@` members are declared.
2. **The verifier** owns the e-graph naming. It mints its own ids for ADT
   constructors / projections / tags and injects the matching reduction rules,
   monomorphizing `Option` on demand. The IR never names these ids.

This document describes the design **as built**. It supersedes an earlier draft
that modelled the IR as an `Exp` tree and proposed lazily-minted per-context
ids; both were corrected during implementation (see §5).

---

## 2. VMIR: a semantic AST (no `@` members)
VMIR is SSA: a body is a list of `Inst { pc: PathConds, kind: InstKind }`, and
`InstKind::Pure(Type, PureInst)` produces one typed value. ADT operations are
**`PureInst` variants**, naming the ADT by its declaration `MemberId` plus
structural indices — never by a synthetic accessor id:

- `PureInst::AdtCons { adt, variant, args }` — construct variant `variant`.
- `PureInst::AdtProj { adt, variant, field, base }` — project a field.
- `PureInst::AdtTag  { adt, base }` — the discriminator (variant index).

Address / snapshot operations reuse existing nodes: a resource address is a
`PureInst::Location` (an `Addr<…>`), and a snapshot read is a `PureInst::Deref`
of that address.

`Declaration::Adt` is purely semantic:

```rust
struct Adt      { variants: Vec<AdtVariant> }     // variant index = tag
struct AdtVariant { field_types: Vec<Type> }
```

No `tag_fn`, no per-field accessor ids. The translator emits `AdtCons`/`AdtProj`/
`AdtTag` at constructor / destructor / discriminator sites and does **not**
emit `@tag` or `@dtor` declarations.

---

## 3. The verifier id registry (`verify::mono`)
`MonoRegistry::build(program)` derives, once per program, a stable id for every
ADT constructor / projection / tag, and the reduction rules over them:

- minted ids start past every real declaration id (`program.interner.len()`), so
  they never collide with a declaration;
- ids are a **deterministic function of declaration order** — the same concept
  gets the same id in every verification context (see §5 for why this matters);
- for each `(adt, variant, field)` it builds a `proj_rule`, and for each `adt` a
  `tag_rule`, mapping each constructor id to its variant index.

Each `VerifyContext` injects the registry's rules into its rewrite/reduce sets,
and `eval_pure_inst` interprets `AdtCons/AdtProj/AdtTag` as `Symbolic::FuncApp`
over the registry id. Names for minted ids (outside the interner) come from the
registry, so visualization never panics.

### `Option` is verifier-internal
`Option` is **not** a VMIR declaration. It is the snapshot-membership type used
by `fold`/`unfold`: each footprint field value becomes `(perm>0) ? Some(v) :
None`. The registry monomorphizes it: scanning predicate snapshots, for each
distinct field (element) type it mints a stable `Some`/`None`/`value`/`tag` id
set and the corresponding reductions. `option_member` / `option_unwrap` resolve
through the registry by element type; the `Option[elem]` value type uses a
reserved verifier `Option` head. No translation-time monomorphization, no
`Program.option_instances`.

---

## 4. Snapshots
A foldable predicate's snapshot is described by `Resource.snapshot`
(`{ addr_fn, cons, projs }`, real declarations). Its projection reductions are
still derived by `verify::meta::derive_adt_meta` (now snapshot-only). Folding the
snapshot into the same registry mechanism is a possible future unification.

---

## 5. Two corrections to the original design

**The IR is SSA, not an `Exp` tree.** The original `Exp::AdtProj`/`Exp::AdtTag`
became `PureInst` variants; a constructor node (`AdtCons`) — absent from the
draft — is required, since projections presuppose a constructor.

**Ids must be program-stable, so monomorphization is *derived*, not lazily
minted per context.** A resource is verified once into a certificate, then
**grafted** at each call site by copying its e-graph nodes (with formal params
substituted by actuals). A node is `FuncApp(id, args)`; if two contexts minted
different ids for the same concept, the grafted nodes would not congruence-match
the caller's. Hence ids are assigned deterministically up front.

Rewrite **rules**, by contrast, *can* be added dynamically: a rule is a
per-context object keyed on an id, a graft transfers proven equalities (not
rules), and a missing rule costs only completeness, never soundness. So a future
on-demand monomorphizer may mint ids lazily **provided** it draws them from a
shared, deterministic concept→id map; the rules can then be injected per context
as concepts appear.

---

## 6. Status and follow-ups
Built and green (`cargo test --lib`): semantic ADT nodes; registry-derived ADT
reductions; Option fully verifier-internal.

Deferred / optional:
- Fold predicate snapshots into the registry (drop the `derive_adt_meta`
  snapshot path).
- Rename `Symbolic::FuncApp/Location`'s `MemberId` payload to distinct
  `FuncId`/`LocId` types — now cosmetic, since the registry already provides the
  indirection.
- Drop the dead constructor `Function` declarations (real Silver decls, now
  unreferenced once `AdtCons` is used).
- Type-argument monomorphization for *user* generic ADTs (none exercised today;
  matches prior behaviour).
