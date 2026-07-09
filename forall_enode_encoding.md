# Foralls as e-nodes: encoding quantifiers directly in the e-graph

Status: design sketch, not implemented. Supersedes-in-spirit the per-quantifier
rule minting in `rewrite.rs` (`PreparedQuantifier` / `quantifier_rule`) if
adopted.

## Idea

Encode each `forall` directly into the e-graph as an ordinary e-node instead of
registering one dedicated rewrite rule per quantifier. A forall e-node has:

- a **recipe reference** (`RecipeId`) — the compiled body + trigger, interned in
  a program-level table; the "code" of the quantifier;
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
| Alpha-equivalent duplicates | duplicated rules and work | deduped at recipe interning + hashcons on (recipe, caps, types) |

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
