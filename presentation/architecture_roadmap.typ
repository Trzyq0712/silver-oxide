// Engineering roadmap: salvage the linearized verifier in place, switch to
// block-based execution only for the residual. Fork of why_switch_architecture.typ.
// Compile: typst compile architecture_roadmap.typ
#set document(title: "A performance roadmap: salvage the linear verifier, blocks for the rest")
#set page(
  paper: "a4",
  margin: (x: 2.2cm, y: 2.2cm),
  numbering: "1",
)
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.62em)
#show heading: set block(above: 1.1em, below: 0.6em)
#set heading(numbering: "1.")

#let eth-blue = rgb("#215CAF")
#let ok = text.with(fill: rgb("#1a7f37"), weight: "bold")
#let bad = text.with(fill: rgb("#c0392b"), weight: "bold")
#show heading.where(level: 1): set text(fill: eth-blue)
#show link: set text(fill: eth-blue)
#show raw: set text(size: 0.92em)

#align(center)[
  #text(size: 16pt, weight: "bold", fill: eth-blue)[
    A performance roadmap for the verifier
  ]
  #v(0.15em)
  #text(size: 11.5pt)[Salvage the linearized architecture in place; switch to blocks only for the residual]
  #v(0.2em)
  #text(size: 9pt, style: "italic")[silver-oxide · ETH Zürich, Programming Methodology Group · 2026-07-18]
]

#v(0.4em)

#block(fill: eth-blue.lighten(92%), inset: 0.9em, radius: 4pt, width: 100%)[
  *The roadmap, in short.* On branching code the verifier is slow and, from 19 match
  arms, #bad[fails outright]. A companion note argues the principled endpoint is a
  *block-based* engine — a path-condition-free ground archive plus small,
  discardable per-block scratch provers. That is still the destination. But the more
  useful near-term finding is this: *most of the cost is recoverable without
  switching architecture.* The two biggest gripes — the per-arm permission
  *partition sum* that only a fragile heuristic collapses, and rewrite rules that
  *fire on everything* — each have a concrete in-place fix on the existing linearized
  CFG: emit the branch join as a permission *select* (a heap ternary) instead of a
  sum, and give the graph *roles* so the expensive rules see only permission terms.
  This document lays out that *salvage plan* first — staged, each step independently
  landable and #ok[forward-compatible] with the endpoint — then names the residual
  gripes that *only* the block-based switch fixes (a monolithic graph that never
  forgets, per-obligation path-condition folding, quantifier pollution across
  sibling branches), and closes with a realistic migration.
]

= What the linearized architecture costs

The pipeline today lowers a method's control flow to *flat, topologically-ordered
VMIR*, verified against *one monolithic e-graph*. The heap is a single *linear
reach-gated thread*: one running heap value threaded through the blocks in
topological order, with each off-path operation's permission gated to zero by its
reaching condition. Values are phi-merged at joins; the heap is not — it accretes
every arm's gated contribution onto the one thread.

The stress test is a Prusti-encoded enum `match` with $N$ arms, each borrowing the
`&mut` target `*v`, converting it, and giving the permission back. Silicon does
$N = 20$ in #sym.tilde 6.5 s; we scale superlinearly and #bad[fail from
$N #sym.gt.eq 19$].

#figure(
  table(
    columns: 8,
    align: (left,) + (right,) * 7,
    stroke: none,
    inset: (x: 0.7em, y: 0.32em),
    table.hline(),
    table.header([$N$], [2], [4], [6], [10], [14], [18], []),
    table.hline(stroke: 0.4pt),
    [our wall (s)], [0.27], [0.40], [0.77], [1.57], [3.37], [*9.54*], [#bad[FAIL 19]],
    [Silicon marginal (s)], [0.6], [—], [2.7], [—], [—], [6.8], [no fail],
    table.hline(),
  ),
  caption: [Enum-match family: superlinear, with a hard ceiling.],
)

Crucially, the obvious culprit is innocent. _"After each arm returns its permission
we cannot merge the fractions back to `1/1`"_ is #ok[false]: a probe on the held
permission at the exit exhale const-folds to `Known(1/1)` at $N = 2, 6, 18$ alike.
Collapse works. The cost decomposes into five distinct gripes — and, tellingly, two
of them are not problems at all.

== The five gripes, tagged

*(a) The permission partition sum — #text(fill: rgb("#1a7f37"))[salvageable].* The
value each arm *constructs and returns* (Prusti's `p_0_Tuple`) does not exist at
entry: every arm builds it, gated by its reach flag, and the single exit merges
them. On the linear thread the held permission is then an *additive sum*
$sum_k "ite"("flag"_k, 1, 0)$ over pairwise-different flags, with *no matching
subtraction*. Reaching $#sym.gt.eq 1$ needs the exhaustiveness fact _"exactly one
flag is set."_ No local rewrite reaches it: `add-sub-cancel` needs a subtraction the
sum lacks, and the identity $"ite"(c,a,x) + "ite"(c,b,y) = "ite"(c,a+b,x+y)$ needs
associative-commutative matching an e-graph does not do as a rule. This is the N≥19
ceiling.

*(b) The rules fire on everything — #text(fill: rgb("#1a7f37"))[salvageable].* Under
pressure to keep the graph small, the rewrite rules push arithmetic and permission
operators down every branch ternary. They fire *globally on every branch-shaped
class*, whether or not the merge they enable is used: on a heap-free 64-arm chain the
rules fire *29 056* times, #bad[92% idempotent] `ite`-reduce steps re-deriving terms
already present. The `ite`/`eq`/`lt` rules are simply too general — they cannot tell
a permission amount from a control guard or a program value.

*(c) The graph never forgets — #text(fill: rgb("#c0392b"))[residual].* The
whole-method history is one serial, ever-growing object every obligation must walk;
each cancelled borrow accretes sum nodes into the `1/1` class. The floor is
$O(N^2)$: ~1000 nodes per arm, never freed, re-saturated per arm.

*(d) Per-obligation path-condition folding — #text(fill: rgb("#c0392b"))[residual].*
The path condition is folded into every obligation *separately*: each `assert` clones
a probe graph, unions in $"pc" #sym.arrow.double "goal"$, and re-saturates it. A
block with $m$ obligations pays $m$ clones and $m$ saturations of essentially the same
state.

*(e) Quantifier branch pollution — #text(fill: rgb("#c0392b"))[residual].* Trigger
instantiations fired inside one arm land in the shared graph and *bleed into sibling
arms* — an unsoundness we currently accept, because the monolithic graph has no
notion of which branch a fact belongs to.

== What is *not* a problem

Two things people expect to be hard collapse cleanly, and the roadmap must not
conflate them with the gripes above.

- *The borrow-return cycle.* An arm that borrows `*v` and folds it back yields a
  per-arm $1 - "ite"("flag",1,0) + "ite"("flag",1,0)$ on the *same* chunk — literally
  $(a - b) + b$, closed by `add-sub-cancel`, #ok[linear] in $N$ (measured clean to
  $N = 24$, zero case splits). A pass-through `&mut` is not a weakness.
- *Exhaustiveness.* The dead `else` arm's `assert false` is discharged natively:
  assuming the path condition, the inhaled variant cover cascades to `false` and the
  class flips `Inconsistent` — no case split, and it survives Prusti's
  snapshot/value encoding split via one domain round-trip axiom.

The lesson: the ceiling is *specifically* the per-arm-constructed return value
(gripe a), and the churn is *specifically* over-general rules (gripe b). Both are
encoding problems, not reasoning limits — and both are fixable in place.

= Salvage: recover most of the performance without switching

Gripes (a) and (b) — the two that actually bite — are fixable on the *existing*
linearized CFG and monolithic graph. The work is staged, each stage independently
landable, and each #ok[forward-compatible] with the block-based endpoint: nothing
here is thrown away when we eventually switch.

== Stage 0 — landed

Eager chunk consolidation folded the `merge_ite_sum` collapse into `merge_chunks`
so held permission returns to the `1/1` class as arms form, not at a late check
(`211c949`): the benchmark went #ok[7.5 s → 2.55 s] and the ceiling from 10 to 18
arms. A pair of `ite`-context-pruning rules that collapse a *select* to `1/1` by
local rewriting shipped opt-in (`SILVER_OXIDE_PRUNE_ITE`, `d3eb26e`). These bought
headroom but did not remove the wall: the collapse still leans on `merge_ite_sum`,
whose core identity the graph cannot key on (Section 1a), so it must *guess* which
terms are the partition and cap the guess with a hand-tuned budget. The fragility
is the residue Stage 1 removes.

== Salvage 1 — the heap-ternary select join (fixes gripe a)

Stop threading one heap and adding gated contributions onto it. Instead *fork* the
heap at a split — each arm starts from the pre-split heap, and works *ungated* under
its own path condition — and *join by a heap ternary*
`HeapInst::Ternary(cond, then, else)`, the phi that `build_entry_env` already builds
for values, lifted to heaps. Read per chunk, the join is
$"ite"("cond", "perm"_"then", "perm"_"else")$.

The payoff: a per-arm-constructed chunk is `1/1` in every arm, so the join is
$"ite"("cond", 1, 1) -> 1$ by the `ite(c,a,a) -> a` fold already in the rule set — a
*select*, not a sum. `merge_ite_sum` is #ok[never invoked]. A borrow-return arm
cancels to `1/1` *inside its own fork* by `add-sub-cancel`. Nested branches produce
nested heap ternaries that mirror the branch tree, so the per-chunk select is
tree-structured and folds locally at any depth (the opt-in context-pruning rules of
Stage 0 handle any redundant gating).

*A free win — address stability.* Forking from the shared pre-split heap means both
arms snapshot against the *same* base, so a snapshot-derived address
(`p_Param(*v)` built from `snap[h]`) is the same e-class in each arm and the
per-chunk join lines up — fixing an instability the additive thread suffers today.

*Surface.* Re-add `HeapInst::Ternary` (removed when the linear thread replaced it —
the IR carried it before) plus the verifier step distributing a permission/deref
lookup through it,
$"perm"("loc", "ite"(c, h, h')) = "ite"(c, "perm"("loc", h), "perm"("loc", h'))$.
Translator: store per-block exit heaps and fork the entry heap (mirror
`build_entry_env`); drop `Sink::gate_perm`.

*The cost it re-incurs.* Heap ternaries make a lookup *branch* — the thing the linear
thread avoided. The trade is deliberate: a branching-but-#ok[local] lookup that
terminating rules collapse, in place of a flat lookup whose permission is an
#bad[AC-hard sum] only a bespoke pass can crack. It does *not* buy the small-state
"forget" benefit (gripes c–e stay); it is purely the sum $->$ select encoding fix.

== Salvage 2 — a `Perm` role and targeted rules (fixes gripe b)

Give the graph *roles*. A permission amount becomes a distinct sort — `Perm`, the
same literals as `Real` (`1/1`, `1/2`, `0`) but a separate world, with its *own*
`ite` and arithmetic e-node variants — bridged to the real world only by explicit,
*uninterpreted* $"real" <-> "perm"$ casts. The permission-collapse rules (the select
fold, the context-pruning, the partition collapse) are written in the perm world,
and because egg buckets e-nodes by their *operator*, they fire *only* on perm classes.
A control or value `ite` is never scanned — the targeting is egg's own matching index,
at #ok[no search cost].

This is *sound by construction*: a perm rule cannot match a real node — a pattern-level
mismatch — and the cast being uninterpreted means nothing crosses unless a rule
bridges it. The sort is a soundness-preserving *restriction* of the true semantics
(`Perm` $equiv$ `Real` underneath); it only narrows what fires. Duplicating a handful
of arithmetic rules across the two worlds is the price, and small — the generic
appliers can be made parametric over the variant so `ite(c,a,a) -> a` stays
single-sourced.

*Two regimes.* Discharge the obligation entirely *inside* the perm world — which
suffices for the overwhelming majority of Prusti's permission goals, whose amounts
are literal `write`s. A cheap syntactic router decides: if the goal's cone touches no
cast it is pure-perm and the targeted regime is complete for it; if it does, the goal
genuinely relates a permission to a program value, and we *re-encode into a generic,
role-free graph* (casts become identity, sorted `ite`s collapse to plain ones) and
retry with the full rule set. Sound because erasing the roles recovers the semantics
they restricted. The re-encode is a *scratch* — a fresh graph, saturated and
discarded — so the role-sorted graph stays the fast working state.

*The same discipline for path conditions.* Reach and branch booleans are their own
role, so pc-directed rewrites target only pc classes and never churn the perm/value
fragments. Roles partition the graph into slices; each rule set sees only its slice;
the expensive rules never touch fragments that cannot use them. This is the direct
answer to gripe (b) — make the rules *un-general by construction*.

*Two axes that multiply.* Salvage 1 is the *structural* axis (a permission is a nested
`ite`, not a sum); Salvage 2 is the *targeting* axis (rules see only that `ite`). A
perm-typed heap select is collapsed by perm-world rules alone, at a cost proportional
to the perm fragment, not the whole method — and with over-firing gone, the Stage-0
pruning rules become cheap enough to default-on.

== After salvage

With Salvage 1–2 the partition wall (a) and the rule churn (b) are gone on the
*existing* linearized CFG — no architecture switch, and `merge_ite_sum` retired to at
most the generic-re-encode fallback. This is expected to remove the N≥19 ceiling and
cut the per-branch churn substantially. What remains is structural.

= What salvage cannot fix: the residual case for blocks

Salvage improves *what fires* and *how a permission is encoded*. It does not change
the *lifetime and scope* of the graph, and the residual gripes are all consequences of
"one monolithic, ever-growing, path-condition-folded graph":

- *(c) Never forgets.* Only a *block-scoped, discardable* graph forgets. Absent that,
  the $O(N^2)$ accretion persists — each block still walks the whole-method history.
- *(d) Per-obligation pc-fold.* A block that assumes its path condition *once* at
  entry discharges all $m$ of its obligations against a *single* saturated graph — no
  per-`assert` clone-and-resaturate. The linear architecture cannot amortize this;
  it has no block boundary to assume the pc at.
- *(e) Quantifier pollution.* Forward-only instantiation — a fact travels *down* the
  block DAG through clone/merge, never *across* to a sibling — is both the performance
  fix and the soundness fix, and it requires per-branch graph identity the monolith
  lacks.
- *Reorder-invariance.* We want a guarantee that reordering independent branches never
  changes the result; only per-arm isolation gives it.

These are exactly the wins the block-based endpoint is designed for — and the reason
salvage, however far it goes, is a floor and not the ceiling.

= The ideal: block-based execution

The endpoint splits the engine into two kinds of graph.

*Ground archive.* An *always path-condition-free* archive holding only facts true in
its region, congruence-compacted, running *only* cheap, shrinking rules plus *all
quantifier instantiation* — never the explosive `ite`-distribution rules. It stays
small and correct as a *representation*. There is not one ground but a *tree*: at a
split the ground is *cloned* per arm; at a join the arms' grounds *merge*. A fact or
instantiation made in an arm is visible only to that arm's descendants and, after the
join, downstream — never to a sibling (fixing gripe e).

*Per-block scratch.* To discharge a block's goals, spin up a scratch as a copy of the
current ground *with the block's path condition assumed once* (fixing gripe d). Small
because the ground is small; short-lived, so it may run heavier rules and is thrown
away with its state (fixing gripe c). What it cannot prove goes to Z3.

*The heap rides each graph, and joins by select.* A chunk is a triple of e-class ids,
so cloning the ground clones its heap; a scratch's pc-justified merges are simply never
written back. At a join the arms' grounds — and their heaps — are merged in a *small,
fresh* scope, where `merge_chunks` consolidates whatever proves equal with no
cross-method residue to guess at.

*Salvage is reused, not replaced.* This is the load-bearing point for sequencing:
block joins *want* the select encoding of Salvage 1 (the join is a per-chunk `ite`,
folded by the same local rules), and the roles of Salvage 2 carry over unchanged. So
the salvage work is the *first half of the migration*, not a detour. The one
assumption the endpoint rests on is *reducible, structured* control flow — a
series-parallel block DAG where every split has a matching join — which Prusti-from-Rust
provides; a cube of $K$ independent diamonds is still structured, joined after each
diamond rather than enumerated as $2^K$ paths.

= Migration: a realistic staged path

#figure(
  table(
    columns: (auto, 1fr, auto),
    align: (left, left, left),
    stroke: none,
    inset: (x: 0.6em, y: 0.4em),
    table.hline(),
    table.header([Stage], [What it lands], [Fixes]),
    table.hline(stroke: 0.4pt),
    [0 · done], [Eager consolidation + `merge_ite_sum`; opt-in `ite`-pruning rules], [partial (a)],
    [1], [Heap-ternary *select* join: fork the heap, join by `HeapInst::Ternary`], [(a)],
    [2], [`Perm` + pc *roles*, targeted rules, generic-re-encode fallback], [(b)],
    [3], [*Block-scoped scratch* graphs: clone/merge grounds, pc assumed once, forget], [(c)(d)(e)],
    [4], [Full block-based VMIR (value naming across join/`old`) + synced Z3 tier], [residue],
    table.hline(),
  ),
  caption: [Each stage is independently landable; salvage (1–2) precedes the
    structural switch (3–4) and is reused by it.],
)

*Ordering rationale.* Salvage first: Stages 1–2 are cheap, high-value, and
forward-compatible — they remove the ceiling and the churn on the architecture we
already have, so the verifier is usable long before the big rewrite. Block-scoping
last: Stage 3 is the largest change and *depends* on the select/role encoding existing
first, so that the ground merges at joins are cheap `ite`-folds rather than the sum
collapse we are retiring. Stage 4 (a concrete block-based VMIR with value names that
survive a join or an `old` read, plus a Z3 state mirroring the ground) is the settled
endpoint; its details are a separate design note.

*De-risking.* Each stage validates an assumption the next relies on. Stage 1 proves
the select encoding collapses permissions by local rules (already demonstrated: the
context rules turn a case split into five local rewrites on the select tower). Stage 2
proves roles cut firing without losing completeness on pure-perm goals. Only then does
Stage 3 commit to per-block graphs, confident the joins it produces are cheap.

= Reference points and honest risks

The two systems we measure against each embody half of the endpoint. *Silicon with
joins* — its default is exponential on $K$ independent `if`s (#bad[$2^K$ paths],
#sym.tilde 4 min at $K = 16$); `--moreJoins 2` collapses the same case to
#ok[#sym.tilde 4 s flat], so the thesis evaluation must compare against `--moreJoins`.
*Silicon's per-path Z3* survives our benchmark by native case splits and by
*forgetting*. The endpoint combines both; salvage buys much of the "forget"-adjacent
win earlier by shrinking *what* the monolith holds and *how often* rules touch it,
even before Stage 3 shrinks *how long* it holds it.

Risks, named: the block-based endpoint may keep *three live representations* (ground,
scratch, mirrored Z3) whose consistency overhead is unclear; *unbounded ground growth*
in a long method (pruning deferred); and *ground–Z3 sync* resting on faithfully
tracking every union and rewrite. The salvage stages carry lighter risk — heap
ternaries re-incur branching lookups (bounded, local), and the `Perm` sort adds a
small rule-duplication and a boundary discipline (keep the perm world closed, which
Viper's literal-only permissions make cheap). None of these undercut the core claim:
*most of the present cost is an encoding problem we can fix in place, and the residual
is what the block-based switch is for.*
