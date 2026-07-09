# Foralls as e-nodes: encoding quantifiers directly in the e-graph

Status: design sketch, not implemented. Supersedes-in-spirit the per-quantifier
rule minting in `rewrite.rs` (`PreparedQuantifier` / `quantifier_rule`) if
adopted.

## Idea

Encode each `forall` directly into the e-graph as an ordinary e-node instead of
registering one dedicated rewrite rule per quantifier. A forall e-node has:

- a **recipe reference** (`RecipeId`) — the compiled body, interned in a
  program-level table with its associated trigger set (see "Node identity"
  below); the "code" of the quantifier;
- **capture children** — ordinary e-class ids for every outer-scope term the
  body/trigger mentions; the "environment";
- **type args in the payload** — for quantifiers under generic domain axioms,
  following the `FuncApp` polymorphic-e-graph convention (types travel as
  payload data, not e-classes).

A **single generic rewrite rule** replaces the per-quantifier rules: it
enumerates forall e-nodes (via `classes_for_op` on the forall discriminant),
matches each one's trigger against the graph, and for every match σ builds the
instantiated body and adds the guarded clause

```
Ite(forall_node, body[caps, σ], true) == true
```

so the instance is released only once the forall's e-class merges `true` —
the same guard discipline the current implementation already uses.

### Encoding choice: compiled recipe, not template sub-graphs

Two encodings were considered:

1. **Template e-nodes**: mirror every operator with an inert "template" variant
   and store the body as a real sub-graph under the forall node. Rejected:
   roughly doubles the `Symbolic` surface, needs congruence-invariant arguments
   ("template classes never merge with concrete classes"), a free-bound-var
   closedness analysis, and capture-avoiding substitution over e-classes for
   nested quantifiers. Buys open bodies (viz, future body rewrites) that
   nothing on the roadmap needs. Also conflicts with the minimal-e-node-encoding
   rule (negation folded into `Ite`, etc.).
2. **Compiled recipe in the e-node** (chosen): the body stays what it is today —
   registry-resolved pure steps + boolean result (`insts: Vec<AxiomInst>` +
   `res`), the trigger stays `trigger_func` + `trig_args`. The e-node carries
   only a `RecipeId` (cheap `Eq`/`Ord`/`Hash`, deterministic, structural dedup
   at intern time) plus capture children and payload types. This is
   `PreparedQuantifier` moved into an e-node: `build_instance`, the `TrigArg`
   positional matcher, and the guard construction all survive nearly unchanged;
   `TrigArg::Capture(c)` reads child `c` of the forall node instead of an
   argument of the opaque occurrence function `Q(caps)`.

### Nested quantifiers: closure conversion, no dynamic recipes

An inner forall inside an outer body does **not** need a value-specialized
recipe when the outer one triggers. Lambda-lift at translation time: intern the
inner recipe once, with a capture slot for every outer-scope thing it touches
(outer binders and outer captures). The outer recipe contains a step
"materialize forall e-node: recipe `k`, capture args = these temps";
`build_instance` resolves the temps through its `vals` map like any other step.
Different σ → different capture children → different e-node; hashcons dedups
repeats. The recipe table is therefore **append-between-runs, frozen
during-run**: recipes are minted only when evaluating VMIR forall instructions
or grafting certificates, never inside `apply_one`.

The one thing values-as-children cannot carry is **types** (not e-classes).
A nested forall under a generic domain axiom keeps its recipe generic and takes
the concrete instantiation through the payload `type_args`, substituted into
the steps at instantiation time — same solution as polymorphic `FuncApp`.

### Node identity, triggers, and alpha-equivalence

The forall e-node's identity is `(RecipeId, type_args, capture children)` —
**the trigger is deliberately not part of it**. A trigger is operational, not
propositional: it controls *when* we instantiate, not what the forall means.
Two foralls with the same body recipe and captures but different declared
triggers denote the same proposition; the guarded release
`Ite(forall, inst, true)` is a tautology of the forall regardless of which
trigger produced the instance. Putting a `TriggerId` in the payload would make
hashcons keep semantically equal foralls in separate e-classes — assuming one
`true` would not release the other's instances. Sound but incomplete, and
dedup lost.

Instead, triggers hang off the table entry: `RecipeId → (body, Vec<Trigger>)`.
Interning a forall whose body dedups to an existing entry **unions the trigger
sets**; the matching rule tries each trigger in the set. Merging trigger sets
is sound (more instantiation opportunities, all guarded); the only cost is
that the union may fire more instances than either declaration alone intended
— a perf concern, not a soundness one.

Alpha-equivalence falls out of recipe interning: binder numbering is already
positional in the step temps, so recipes are alpha-canonical for free.
Canonicalizing capture-slot order (by first use in the steps) at intern time
additionally dedups capture permutations, cheaply. Limits:

- Dedup is syntactic-after-canonicalization, not semantic — `x+1` vs `1+x`
  bodies do not merge (bodies are inert data; no rewrites reach them). Fine.
- Recipe dedup does **not** skip WD: Silver well-definedness is
  per-occurrence, and a second occurrence of a shared recipe may sit under
  different ambient facts, so the scratch check runs per syntactic
  occurrence regardless of the shared `RecipeId`.

### Heap-dependent functions in quantifier bodies

The design's hard invariant: **recipes are pure — assert-free and heap-free**.
Instantiation runs inside `apply_one`, which can only add guarded facts; it
cannot read the verifier-side symbolic `Heap` (chunk maps are not e-classes)
and cannot discharge obligations. `PureInst::Snap` violates both — it walks
the symbolic heap and implicitly *asserts* footprint sufficiency + the
resource bool — so a live `Snap` step over bound variables is unbuildable in a
recipe. Consequences:

- **Binder-independent footprints work — freeze the heap at encounter.** If
  the called function's footprint does not depend on the binders (its args may
  still mention them in non-footprint positions), evaluate the `Snap` once at
  quantifier-encounter time against the heap at that program point. The
  resulting snapshot value `s` is an ordinary e-class → a **capture child**;
  the body step becomes a plain pure `f(args, s)`. Semantically exact:
  a heap-dependent forall assumed at a state only constrains `f` at that
  state's snapshot. Triggers on `f` work — the snapshot position is a
  `TrigArg::Capture`, and congruence handles "same heap contents, different
  program point" (equal snapshot values unify, matches fire).
- **Binder-dependent footprints break down — loudly.** `forall x :: f(x) > 0`
  with `requires acc(x.f)` needs a snapshot per instance over an
  `x`-dependent footprint: that is quantified permissions (Phase 4, not
  designed). Encounter-time evaluation of the `Snap` does a syntactic chunk
  lookup at `addr(x_fresh)`, finds nothing, and rejects — a translation
  error, not unsoundness. Same frontier as the rest of the system.
- **Foralls inside heap-dependent function bodies are free.** Function bodies
  are purified against `H(s)` (`eval_snap`/`eval_from_snap`): every deref is
  already a pure term over `proj(s)` when a nested forall is encountered, so
  its recipe captures `s`-projections like any other outer term. No special
  case.
- **WD unaffected**: everything assertive resolves either at encounter (the
  frozen `Snap`'s footprint check, in the main graph) or in the scratch clone
  with fresh binders (resource bool, body side conditions). Nothing assertive
  survives into a recipe, so instantiation stays obligation-free.

#### The QP boundary: binder-dependence of footprint slots

The binder's *type* is irrelevant to whether a quantifier needs quantified
permissions — what matters is where the binder flows. `forall i: Int` calling
`f(i)` with `requires acc(P(i))` is QP (one distinct slot per binding, no
`Ref` in sight; likewise via indirection, `acc(lookup(a, i).val)`);
`forall r: Ref` calling an `f` that requires `acc(P())` is not (constant
footprint, snapshot once).

Precisely: a footprint slot = (address, permission amount) computed by
evaluating `f#requires` at the call args. The quantifier crosses into QP
territory iff, after evaluation with binders as fresh values, some slot's
**address or perm amount** still mentions a binder. Three sharpenings:

1. It is the *slot* that matters, not the call and not the value read —
   binders in non-footprint argument positions are fine (they flow into the
   pure `f(args, s)` call, the heap is untouched).
2. The *semantic* boundary is after-simplification, not syntactic:
   `acc(P(i - i))` mentions `i` but the address normalizes to `P@addr(0)` —
   a snapshot would work. Enforcement, however, is syntactic (see
   "Translation-time detection" below), so such cases are conservatively
   rejected.
3. A binder-dependent precondition **bool** is *not* QP. With a constant
   footprint but `f#requires` bool `i > 0`, the heap part snapshots once;
   the bool cannot be asserted once at encounter (it mentions `i`), so it
   shifts into the WD obligation — proved in the scratch clone with the
   fresh binder under ambient facts (e.g. discharged by the body's own
   guard in `forall i :: i > 0 ==> f(i) > 0`, subject to how
   implication-guarded WD is threaded — same shape as the deferred-WD
   plan). Only the *spatial* part draws the QP line.

##### Translation-time detection

The boundary is enforceable at **translation time by construction**, because
framing already lives there: footprint sufficiency is decided by the
frontend's syntactic state tracker (Pillar 1 — `HashSet` of available
resource instances, syntactic-equality lookup, compile error on miss).
Translating a forall body with binders as opaque locals, emitting the `Snap`
requires finding `f`'s footprint chunks in the tracker; an address mentioning
a binder matches nothing ever held → `TranslationError`. The failure is the
detector — no separate classifier is needed for *soundness*.

Note this check is purely syntactic (translation has no e-graph), hence
strictly more conservative than the semantic boundary above: `acc(P(i - i))`
is rejected even though semantically constant. Acceptable while QP is
unsupported — every rejection is of something unsupported anyway, so no
completeness is lost until QP lands.

For a *good error message*, add a targeted classifier: a per-function
**footprint-dependency summary**, computed once when lowering `f#requires` —
the set of parameters that (transitively) reach an `Acc` address argument or
a perm expression. At forall lowering, binder dataflow into a call arg whose
parameter is footprint-relevant → a dedicated "this quantifier needs
quantified permissions" error instead of a generic missing-permission framing
error. Covers indirection (`lookup(a, i)` — the arg contains the binder) and
perm-amount dependence (the summary includes perm exprs). Pure syntactic
dataflow, one pass, decidable.

Caveat for later: the translation-time line is stricter than what
Viper/Silicon accept — they check WD semantically and can admit a
binder-dependent-looking footprint that is provably framed (by a held QP, or
a provably constant address). When QP support lands, the check either moves
partly to verify time or the conservative line is kept deliberately.

This matches Viper's line: a pure forall calling a heap-dependent function is
legal without QP exactly when the precondition's permissions are provable for
all bindings from the currently held, non-quantified chunks — a constant
footprint qualifies; per-binding distinct slots require a held
`forall … acc(…)` (a real QP) to frame them.

### Recipe table placement

- **Ownership: program level**, owned by `verify::verify` next to
  `FuncRegistry` / `fn_certs` (or as a `FuncRegistry` field): recipe ids must
  stay stable across units because certificate grafting replays recipes in
  later contexts and nested recipes reference inner ids by `RecipeId`. Table =
  `TiVec<RecipeId, QuantRecipe>` + dedup `HashMap<QuantRecipe, RecipeId>`.
- **Access during saturation: `Arc` snapshot** held by the single quantifier
  rule, rebuilt at saturation time — the same lifecycle as the per-unit
  `axiom_rules` and the ADT rules pulled from `FuncRegistry`. egg appliers are
  `'static`, so no borrowing; freezing during runs makes a plain `Arc` enough.

### Well-definedness: clone-the-graph scratch check

WD of a quantifier body is checked **once per syntactic quantifier**, at
encounter time: clone the current e-graph (O(graph size), ids survive), rebuild
the rule set over the clone, introduce fresh values for the binders, and
discharge the body's side conditions in the scratch graph. Cloning (rather than
a blank scratch graph) makes all ambient facts — path conditions, axioms,
certificate-derived knowledge — available for free, with no seeding policy and
no pollution of the main graph. Nested quantifiers are checked recursively in
the same scratch pass (outer binders already fresh); dynamically materialized
forall nodes never re-check WD — they are instances of already-checked
templates, so no nested-runner-inside-applier problem arises. Stateful applier
caches must not be shared between the scratch run and the main run.

## Comparison with the current implementation

| | Current (`PreparedQuantifier` + minted rules) | Forall-as-e-node |
|---|---|---|
| Quantifier registration | one egg `Rewrite` per quantifier, minted **before** the runner starts | one generic rule; quantifiers are data |
| Quantifiers created mid-run | impossible (egg forbids rule injection mid-run) → eager transitive preload workaround; breaks for quantifiers arriving via cert grafts | next iteration of the generic rule sees the new node — works by construction |
| Occurrence tracking | opaque occurrence function `Q(caps)`, explicit capture arity, occurrence enumeration loop | the forall e-node *is* the occurrence; captures are children, canonicalized by congruence, deduped by hashcons |
| Body storage | side-table (`insts` inside the rule's applier) | side-table (recipe table), but referenced from an ordinary e-node — certificates serialize it uniformly |
| Guarded release | `Ite(Q(caps), res, true) == true` | identical |
| Trigger expressivity | single flat func app | same restriction; the recipe has a natural home for future generalization but does not deliver it |
| Instantiation memo | per-rule seen-set, perf-only | still perf-only, not needed for soundness/termination (instances are idempotent; `union` returns `false` on repeats). Can be dropped initially; expect to reintroduce a seen-set keyed (forall class, σ) as the first perf fix |
| WD checking | deferred entirely | once per syntactic quantifier via graph-clone scratch check |
| Assert-side foralls | no path (assume-only) | representable: skolemize with fresh consts, union the forall node with `true` if the body proves — future work, but the design has a home for it |
| Alpha-equivalent duplicates | duplicated rules and work | deduped at recipe interning + hashcons on (recipe, caps, types); triggers excluded from identity, trigger sets unioned on the recipe entry |
| Heap-dependent calls in bodies | n/a (pure foralls only) | binder-independent footprints via encounter-time snapshot capture; binder-dependent footprints rejected (need QP, Phase 4) |

## Wins

1. **Dynamic quantifiers mid-run** — the main one. Kills the eager-preload
   workaround; quantifiers materialized by outer instantiation or certificate
   grafting become triggerable within the same runner call.
2. **No per-quantifier rule registry**; a forall is a value. Certificates
   (`BodyRecipe`/`SeedRef`) carry forall nodes like any other term.
3. **Capture bookkeeping collapses** — no occurrence function, no capture
   arity, no occurrence-enumeration loop; congruence and hashcons do the work.
4. **WD becomes checkable** (and cheap: once per syntactic quantifier, not per
   instance).
5. **A path to assert-side foralls** exists in the representation.
6. **Mostly a refactor, not a rebuild**: recipe format, `build_instance`,
   `TrigArg` matching, and the guard survive.

## Known non-wins and open issues

- **Branch-pollution bug unchanged.** The guard discipline is identical to
  today's; the pollution comes from an occurrence's truth being global once
  merged `true`, which this redesign does not touch.
- **Trigger expressivity unchanged** (single flat function application). Deep
  or multi-triggers need real e-matching machinery either way.
- **Termination surface widens**: instantiation can mint new forall nodes which
  instantiate in turn. Today's preload bounded the quantifier population
  statically; the new design is unbounded and will eventually want a
  depth/budget cap on top of the seen-set.
- **Scheduler**: one heavy generic rule fits egg's `BackoffScheduler` poorly
  (nondeterministic throttling). Cheaper first lever: `Runner::with_hook` —
  saturate the cheap rules, fire quantifier instantiation between iterations as
  an outer fixpoint. A custom scheduler only if that proves insufficient.
  Aggregate matching cost is not obviously worse than today: N per-quantifier
  rules each scanning their trigger op ≈ one rule scanning N triggers.
- **Memo staleness wart carries over**: seen-set keys canonicalized at insert
  can duplicate after later merges — benign (idempotent instances), same as
  today.
