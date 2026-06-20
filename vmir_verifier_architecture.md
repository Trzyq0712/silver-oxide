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

- `PureInst::AdtCons { adt, type_args, variant, args }` — construct variant `variant`.
- `PureInst::AdtProj { adt, type_args, variant, field, base }` — project a field.
- `PureInst::AdtTag  { adt, type_args, base }` — the discriminator (variant index).

`type_args` is the ADT's monomorphization (empty for non-generic), filled by
translate from the use-site typed types, so the verifier needs no per-value type
environment. `Type::Generic(usize)` denotes a type parameter inside a generic
ADT declaration.

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

## 3. The verifier id allocator (`verify::mono`)
The e-graph is **disconnected from VMIR `MemberId`**: `Symbolic::FuncApp` carries
a `FuncId` and `Symbolic::Location` a `LocId` (`verify::lang`). A plain function
or location reuses its declaration index as its id; ADT constructor / projection
/ tag ops get **freshly-minted** ids.

`Allocator` (owned by `verify::verify`) mints these **lazily on first use** of a
monomorphic instance `(adt, type-args)`:

- minting an instance mints its tag + every constructor + every projection, and
  appends their `proj_rule`/`tag_rule` reductions; minted ids start past every
  real declaration id;
- monomorphization is keyed by `(adt, type-args)`: a non-generic ADT is the
  empty-args instance; a generic ADT (user-written or `Option`) gets one instance
  per concrete type-argument tuple, discovered on use;
- the allocator is threaded **`&mut`** through each (sequential) verification
  unit — no interior mutability — so an instance keeps the **same** id wherever
  it appears. This is what makes certificate grafting sound: `transplant` copies
  cert nodes carrying the id verbatim (see §5).

`VerifyContext::saturate`/`reduce` use the static rules plus `alloc.rules()`
(which grows as instances are minted). `eval_pure_inst` interprets
`AdtCons/AdtProj/AdtTag` via `alloc.cons/proj/tag`. Names for minted ids come
from the allocator's reverse table (`ctx.func_name`), so viz never panics.

### `Option` is a builtin generic ADT
`Option` is an ordinary generic ADT — there is **no** Option-specific
monomorphization machinery. It is a **builtin**, injected on verifier entry
(`verify::prelude::with_prelude`, like a Rust lang item) rather than produced by
translation, so directly-authored VMIR is valid too. The injected declaration is
`Adt { variants: [ Some{Generic(0)}, None ] }`, interned under the well-known
name `"Option"`.

It is used as the snapshot-membership type by `fold`/`unfold`: each footprint
field value becomes `(perm>0) ? Some(v) : None`. The only Option-specific thing
in the backend is that it **queries the Option ADT's id**
(`registry.option_adt()`); from there the general `(adt, type-args)`
monomorphization applies — the registry instantiates `Option[elem]` at each
predicate-snapshot element type. `option_member`/`option_unwrap` are thin
helpers over `registry.cons`/`registry.proj` for that ADT.

---

## 4. Snapshots
A foldable predicate's snapshot is a **single-variant ADT** in the allocator,
keyed by its `@snap` Domain id. `Resource.snapshot = { addr_fn, snap, field_types }`
is semantic — no `cons`/`proj` declarations. fold/unfold build and recover it via
`alloc.cons/proj` like any other ADT. (There is no `verify::meta`.)

---

## 5. Two corrections to the original design

**The IR is SSA, not an `Exp` tree.** The original `Exp::AdtProj`/`Exp::AdtTag`
became `PureInst` variants; a constructor node (`AdtCons`) — absent from the
draft — is required, since projections presuppose a constructor.

**Ids must be consistent across contexts, but may be allocated lazily.** A
resource is verified once into a certificate, then **grafted** at each call site
by copying its e-graph nodes (with formal params substituted by actuals). A node
is `FuncApp(id, args)`; if two contexts used different ids for the same instance,
the grafted nodes would not congruence-match the caller's. The allocator solves
this not by pre-deriving everything, but by being **shared** (`&mut`-threaded,
owned by `verify::verify`): the same instance is minted once and reused, so its
id is consistent wherever it appears. Contexts run sequentially, so a plain
`&mut` suffices.

Rewrite **rules** are likewise fine to add dynamically: a rule is keyed on an id,
a graft transfers proven equalities (not rules), and a missing rule costs only
completeness, never soundness. Each context's `saturate` pulls the allocator's
current rules, so instances minted while building a cert are available to later
units.

---

## 6. Status and follow-ups
Built and green (`cargo test`, 109 lib + 2 suite): semantic ADT nodes with
`type_args`; a lazy `&mut`-shared allocator; predicate snapshots and `Option` as
ordinary ADTs in it; `Option` a builtin injected on verify entry; the e-graph on
distinct `FuncId`/`LocId` (no `MemberId`); general user generic ADTs verify.

Deferred / optional:
- Drop the dead constructor `Function` declarations (real Silver decls, now
  unreferenced once `AdtCons` is used).
- Use-site `type_args` for `AdtProj`/`AdtTag` over *user* generic ADTs is taken
  from the destructor/discriminator base's typed type at lowering; the allocator
  already supports it. (`AdtCons` keys off its result type.)
- Location result types are no longer reconstructed by `infer_type` (returns
  `None` for addresses); `heap_acc` falls back to `Int` for the held-value type
  (viz/inference cosmetics only — not soundness).
