// Argument document: stop forcing the e-graph to prove; store in a ground, prove in scratches.
// Compile: typst compile why_switch_architecture.typ
#set document(title: "Scaling the verifier: store in the e-graph, prove in the small")
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
    Scaling the verifier
  ]
  #v(0.15em)
  #text(size: 11.5pt)[Stop forcing the e-graph to prove — store in a ground, prove in the small]
  #v(0.2em)
  #text(size: 9pt, style: "italic")[silver-oxide · ETH Zürich, Programming Methodology Group · 2026-07-17]
]

#v(0.4em)

#block(fill: eth-blue.lighten(92%), inset: 0.9em, radius: 4pt, width: 100%)[
  *The argument, in short.* On branching code the verifier is slow and, from 19
  match arms, #bad[fails outright]. The cause is not a missing optimization —
  permission collapse already works — but that we are using the e-graph against
  its grain. We ask one ever-growing graph to _prove_ things e-graphs are bad at,
  mainly case splits and arithmetic. The rules that let it try — mostly
  `ite`-distribution — bloat the graph without closing the goals we want, and the
  only reason matches verify at all is a heuristic collapse that guesses at term
  shape and had a soundness bug. The proposal is to stop. An e-graph is very good
  at _representing_ information, compacting it as it learns, holding recursive
  data, and firing quantifier instantiations; it is a poor general prover. So we
  keep a *ground* graph as a path-condition-free _archive_ that runs only cheap,
  shrinking rules plus quantifier instantiation, and spin up *small scratch* graphs
  — path condition assumed, free to run heavier rules — to discharge each block's
  goals. What a scratch cannot prove goes to Z3; if Z3 also fails, we fail. (A
  strictly Z3-less mode can instead note the goal and continue — fast but
  incomplete.) Blocks are independent, which buys small state and no quantifier
  pollution.
]

= The real problem: forcing the e-graph to prove what it is bad at

The benchmark is a Prusti-encoded enum match with $N$ arms, each borrowing `*v`
and giving the permission back. Silicon does $N = 20$ in #sym.tilde 6.5 s; we scale
superlinearly and #bad[fail from $N #sym.gt.eq 19$]. The obvious guess —
_"after each branch returns its permission we cannot merge the fractions back to
`1/1`"_ — is *false*: a probe on the held permission at the exit exhale const-folds
to #ok[`Known(1/1)`] at $N = 2, 6, 18$ alike. Collapse works. The real problem is
that we run a general prover inside a structure that was never meant to be one.

#set enum(numbering: "1.", spacing: 0.85em)

+ *The rules have grown complicated, and they bloat the graph.* Under pressure to
  keep the graph small, our rewrite rules have deteriorated into heavier and
  heavier machinery — the worst offender pushes arithmetic and permission operators
  *all the way down* a branch ternary chain, distributing them through every `ite`
  so a cross-arm merge becomes possible. This is the main source of churn: on a
  *heap-free* 64-arm branch chain — a separate benchmark that reproduces the same
  wall with *no heap at all*, so the cost is the branching, not the permission
  bookkeeping — the rules fire *29 056* times, *92% of them idempotent* `ite`-reduce
  steps re-deriving terms already there. They fire globally on every branch-shaped
  class, in a graph that never forgets, whether or not the merge they enable is
  ever used. Taking this pressure *off* egg is where we expect to get faster.

+ *And they still do not close the goal.* The residual is *not* the borrowed `*v`
  above — that collapses. It is the value each arm *constructs* and returns
  (Prusti's `p_0_Tuple`): born fresh inside every branch, it reaches the exit as a
  sum $sum "ite"("flag"_k, 1, 0)$ over *pairwise-different* conditions, with no
  subtraction to cancel against. Proving $#sym.gt.eq 1$ needs _"exactly one flag is
  set"_ — an $N$-deep case split an e-graph cannot do natively (dissected in
  Section 1.3). We fake it with more rules and deeper saturation, pay for it in the
  bloat above, and *still fail*. Pushing egg harder here does not help.

#v(0.2em)

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
  caption: [Enum-match family: superlinear, with a hard ceiling that is the
    per-arm return-value partition sum — not exhaustiveness, not the borrow-return,
    both of which collapse cleanly (Section 1.3).],
)

== Why the case split is so slow

When saturation cannot close a goal we fall back to an explicit case split (the
tier-4 prover). It is slow for a structural reason: to try splitting on a
condition it *clones the entire probe graph*, unions the condition to `true`,
*re-saturates the whole clone*, then does the same for `false` — and recurses,
nesting splits to some depth. Every node is a fresh full graph plus a full
saturation; nothing is shared between arms. The cost is exponential in the split
depth times the number of candidate conditions, and we cap it with a hand-tuned
budget (384 probe saturations per goal) so an unprovable goal at least gives up
gracefully. Doing case analysis this way — clone-and-resaturate — is the most
expensive shape possible, and it exists only because the e-graph has no cheaper
way to branch.

== And matches verify only because of a fragile heuristic

$N$-arm matches verify at all only because of a hand-written pass that collapses
the permission sum. Its core is a clean identity,
$"ite"(c,a,x) + "ite"(c,b,y) equiv "ite"(c, a+b, x+y)$ — but the graph does not hand
it a clean sum to work on. A permission class holds the real partition sum *and*
leftover terms like `x = (x - p) + p`, and the two are indistinguishable to the
e-graph, which erases term identity by design. So the pass has to *guess* which
terms are the partition by their shape, and cap its work with a hand-tuned budget.
It happens to work on the shapes we generate, but it is guesswork bolted onto a
structure that gives it nothing to key on.

None of this is essential. It is the price of forcing a proof obligation through a
shared, unbounded, path-condition-carrying graph. Shrink the scope, assume the
path condition inside it, and the sum is clean — nothing to guess at, no budget to
tune.

== What we can already prove: exhaustiveness up to arithmetic

Two obligations hide under "exhaustiveness," and only one is a real e-graph
weakness — a distinction worth drawing precisely, because the common one we
handle *well*. Measured on the isolated enum-match dead arm (heap stripped, $N$
arms, tier-4 case split *disabled*):

- *The dead-arm cover.* Every `match` Prusti compiles has an `else` it proves
  unreachable: under $and.big_k not "cond"_k$, derive `false` from the inhaled
  variant cover $or.big_k "cond"_k$. The e-graph does this *natively and with no
  case split*: assuming the block's path condition, the disjunction tower
  `ite`-cascades to `false` and the class flips #bad[`Inconsistent`]. It survives
  Prusti's snapshot/value encoding split — cover in constructor form
  `s == cons(k)`, branch in extracted form `value(s) == k` — because one domain
  round-trip axiom, `value(cons(k)) == k`, fires by trigger and bridges the two.
  Empirically it is #ok[linear]: $N = 320$ discharges in #sym.tilde 0.1 s of
  proving, `sat_iterations` flat at 6, *zero* case splits — the only
  superlinearity is the unrelated $O(N^2)$ IR bloat (C1).
- *The borrow-return cycle.* Each arm borrows a resource it *entered* with (the
  `&mut` point `*v`), converts it, and folds it back — a per-arm
  $1 - "ite"("flag", 1, 0) + "ite"("flag", 1, 0)$ on the *same* chunk. This
  collapses #ok[natively] by `add-sub-cancel` ($(a - b) + b -> a$): no case split,
  no partition fact, #ok[linear] in $N$ (measured clean to $N = 24$,
  `add-sub-cancel` firing $N + 1$ times, zero tier-4). A borrowed-and-returned
  `&mut` is *not* a weakness — the two `ite`s are one hash-consed class and cancel.
- *Parallel value construction — the one genuinely hard shape.* The value each
  arm *returns* (Prusti's `p_0_Tuple`) does not exist at entry: every arm
  *constructs* it fresh, gated by its reach flag, and the single exit merges the
  arms. The held permission is then $sum_k "ite"("flag"_k, 1, 0)$ — a partition
  *sum* with *no matching subtraction*, so `add-sub-cancel` has nothing to grab,
  and reaching $#sym.gt.eq 1$ needs the exhaustiveness fact _"exactly one flag is
  set."_ *This* is the genuine case split of Section 1, and #bad[the sole reason]
  the benchmark fails from $N #sym.gt.eq 19$ — not the cover, not the borrow-return.

The dividing line is precise: a resource *passed through* the branches (borrowed
and given back) cancels by a local rule; a resource *born inside* the branches and
joined at the exit does not. And the root is an *encoding*, not a reasoning limit.
A gated additive thread turns the join into a `+`-spine of `ite`s, and collapsing
$sum_k "ite" = 1$ needs associative-commutative matching the e-graph does not do
as a rule — today a bespoke `merge_ite_sum` procedure supplies it, capped by a
hand-tuned budget (C2). Express the *same* merge as a *select* —
`ite(flag_0, 1, ite(flag_1, 1, ... 1))`, one arm per branch, each already $1$ —
and it folds by the trivial local rule `ite(c, a, a) -> a`: no partition fact, no
AC matching. Selecting rather than summing at the join (a heap-phi) is the one
lever that retires both `merge_ite_sum` and the $N$-wall.

So the honest claim: *we solve the usual match exhaustiveness and every
borrow-return cycle — finite variant covers, boolean- and congruence-shaped,
plus pass-through resources — with no prover at all.* What we do not
get for free is any exhaustiveness resting on *arithmetic*. An integer-interval
match (`< 0`, `== 0`, `> 0`) closes its `else` only by trichotomy; a gapped
partition (`<= 0`, `>= 1`) only by integer-specific reasoning about the empty
interval between the guards. The e-graph has no order theory — and, the sharp
point, *case-splitting does not rescue these either*: splitting an `ite`
condition leaves arithmetic residue nothing in the rule set can fold, so they
fail #bad[even with tier 4 on]. These are Z3 obligations, full stop. (A *binary*
interval split slips through only because `>=` is exactly the negation of `<`,
making its `else` one atom asserted both true and false — boolean, not
arithmetic.)

#block(fill: gray.lighten(90%), inset: 0.8em, radius: 4pt, width: 100%)[
  *Completeness against spec-free Prusti is not the bar.* Prusti compiling
  *unannotated* Rust necessarily emits obligations whose validity rests on
  arithmetic the pattern desugaring introduces — the interval matches above,
  overflow/wraparound (`%`) terms, and their kin. No amount of equality
  saturation discharges these, and it is no defect that it cannot: they are
  exactly what the Z3 tier (or, in Z3-less mode, the honest note-and-continue) is
  for. The claim is never that the e-graph proves everything Prusti generates — it
  cannot, and Section 1 is the cost of trying — but that it discharges the large
  congruence-shaped bulk cheaply and routes the arithmetic residue to a solver
  built for it.
]

= What the e-graph is good at — and the proposal

An e-graph is not a prover; it is a *data structure for equalities*. Its real
strengths:

- *Representing information compactly, and compacting it further as it learns.*
  Once $x = y$ is known, congruence merges $x.f$ and $y.f$ and every term built
  over them, for free. This is the permission-consolidation win, and where the
  tool shines.
- *Holding recursive, structured data* — snapshots, ADT round-trips, function
  bodies — as shared sub-terms instead of duplicated trees.
- *Quantifier instantiation.* E-matching over congruence is a good instantiation
  engine, and one we control far better than an SMT solver's: we choose when
  triggers fire, we carry instantiated facts across graph boundaries, and we can
  *merge* two graphs' quantifier states cleanly.

The weaknesses are the mirror image: *case splits*, *arithmetic*, and genuine
*disjunction* — anything that needs the solver to _choose_ rather than
_saturate_. Exhaustiveness is deliberately *not* on this list: as the previous
subsection shows, the usual finite variant cover collapses by congruence with no
choice at all; it turns hard only when its `else` rests on arithmetic, or when the
disjunction is a permission partition over independent flags. Section 1's
permission sum is one such instance.

#block(fill: eth-blue.lighten(92%), inset: 0.85em, radius: 4pt, width: 100%)[
  *The proposal.* Use the e-graph as *information storage with lightweight
  proving*, not as a general prover. Let it represent and compact what we know and
  fire quantifier instantiations; do *not* strain it to discharge case splits,
  exhaustiveness, or non-linear arithmetic. When light reasoning is not enough,
  hand the goal to Z3. This is the ceiling; we should not push the e-graph past it.
]

= The design: a ground archive and small scratch provers

The proposal splits the engine into two kinds of graph.

*Ground e-graphs.* An archive that is *always path-condition-free*: it holds only
facts true in its region, in the shared, congruence-compacted form the tool is good
at, with *no* path-condition ternaries or guards — the region context is implicit,
not written into the terms. It runs only *cheap* rules — congruence, plus *reductive
(subexpression) rewrites* that can only *shrink* the graph by folding a term into an
equal, simpler one that congruence then dedups — together with *all quantifier
instantiation*. It never runs the explosive `ite`-distribution rules. So it stays
small and correct as a *representation*.

There is *not one* ground but a *tree* of them. At a branch's *split point* the
current ground is *cloned*, one copy per arm; each arm then extends its own clone
independently. At the *join point* the arms' grounds are *merged* back into one. So
a fact learned or a quantifier fired inside an arm lives in that arm's ground clone
and is visible only to that arm's *child* blocks and, after the join, downstream —
never to a sibling arm. This is the whole point of keeping grounds pc-free and
per-region: see below.

*Scratch e-graphs.* To discharge a region's goals, spin up a scratch as a copy of the
current ground, *with the region's path condition assumed*. It is small because the
ground it copies is kept small. Being short-lived and scoped to one path, it can
afford heavier
saturation than the ground: whatever a goal needs is run at a scale bounded by the
scratch and thrown away with it. Exactly which rules run where is left open — the
point is that the cost stays local. The scratch proves what it can; the ground never
pays for the attempt.

Assumes and asserts bridge the two: on an `assume`/`assert` we *also* record the
learned fact into the current region's ground. No pc guard is needed — the arm's
ground clone already *is* the branch context, so the fact goes in flat, keeping the
ground pc-free.

== The heap rides each graph

The heap is *not a separate engine* to split alongside the graphs — it already
lives inside them. A heap chunk is a triple of e-class ids (`addr`, `perm`,
`value`), so it belongs to whichever graph holds those classes. Splitting the graph
therefore splits the heap for free: a *ground heap* sits on the ground, a *scratch
heap* on each scratch clone, no second mechanism required.

The split buys the same win at the heap level that it buys for permission sums.
The *ground heap* is a pc-free chunk archive: it must keep `acc(x.f)` and `acc(y.f)`
apart, and keep ite-guarded permissions guarded, because it may not assume the
branch that would let them collapse. The *scratch heap* is those same chunks with the
pc assumed — so congruence merges the two `addr` classes under `x == y` and the
chunks consolidate to a single `1/1`, a merge the ground is *not allowed* to make.
This is the heap-level twin of the permission-sum collapse of Section 1: don't
force the pc-free archive to merge what only the branch justifies; do it in the
scoped copy that may assume the branch.

The discipline is the mirror of "grounds stay pc-free": *prove in the scratch, update
state in the ground.* Sufficiency of an exhale is shown in the merged scratch view,
where the aliased chunks are one; the resulting held state is then written back in
the ground's *unmerged, guarded* form, so a pc-derived merge never contaminates the
archive.

*`old` reads fall out of the same structure.* An `old(e)` evaluates `e` against an
earlier heap state, and the ground archive already holds that state — the ground as
it stood at that program point. To evaluate the `old` expression, take that archived
ground and assume the *current* pc in it, exactly as we seed any scratch. The old
state and the current one share the same construction; only which archived ground we
copy from differs.

== Collapsing the join: select, not sum

At a join the arms' held permissions must recombine into the exit amount. *How*
they recombine — not any reasoning power — decides whether the proof closes by
local rewriting or needs the one bespoke pass we would most like to retire. It is
fixed entirely by the join's *shape*.

*Two shapes for the same value.* Take a resource each arm holds at `1/1` — the
returned `p_0_Tuple` of Section 1, or any chunk *constructed* per arm. Reassembled
at the join it is one of:

- an *additive sum* $sum_k "ite"("flag"_k, 1, 0)$ — the linear-thread encoding,
  where each arm's gated contribution is *added* onto one running chunk;
- a *select* $"ite"("flag"_0, 1, "ite"("flag"_1, 1, … 1))$ — the heap-join
  encoding, where the merge *chooses* the live arm's chunk instead of summing.

Both denote the exit permission. They are worlds apart for the e-graph.

*The sum collapses only through `merge_ite_sum`.* $sum_k "ite" = 1$ holds only
because the flags partition — _"exactly one is set."_ No local rewrite reaches it:
`add-sub-cancel` needs a matching subtraction the sum does not contain, and the
identity $"ite"(c,a,x) + "ite"(c,b,y) = "ite"(c, a+b, x+y)$ needs *associative-
commutative* matching over the `+` spine, which an e-graph does not do as a rule.
The hand-written `merge_ite_sum` pass exists precisely to flatten the spine and
group summands procedurally. #bad[We confirmed this is the *only* path:] disabling
the pass, the $N #sym.gt.eq 3$ arm partitions fail outright ($N = 8$: FAIL), with
no other rule or const-fold taking up the slack.

*The select collapses by local rewrite.* A select is a *nested `ite`*, and nested
`ite`s fold syntactically. Two unconditional identities — the inner condition *is*
the outer one's e-class, so it is fixed inside each branch — do it, alongside the
fold $"ite"(c, a, a) -> a$ already in the rule set:

$ "ite"(c, "ite"(c, a, b), e) &-> "ite"(c, a, e) quad #text[(then-context)] \
  "ite"(c, t, "ite"(c, a, b)) &-> "ite"(c, t, b) quad #text[(else-context)] $

No AC matching, no partition fact, no case split. They only ever *shrink* an `ite`
nest, so they terminate — the opposite of Section 1's distributive rules.

=== Walkthrough: reaching `1/1` in both regimes

*Select regime (heap join), if-else.* Each arm holds the chunk at `1/1`; the merge
selects. Even the redundantly-gated form a naive lowering emits collapses:

$ &"ite"(c_0, thin "ite"(c_0, 1, 0), thin "ite"(c_0, 0, 1)) \
  &quad ->^#text[then-ctx] quad "ite"(c_0, thin 1, thin "ite"(c_0, 0, 1)) \
  &quad ->^#text[else-ctx] quad "ite"(c_0, thin 1, thin 1) \
  &quad ->^#text[$"ite"(c,a,a)$] quad 1 $

Nesting deeper is the same cascade *provided the join mirrors the branch tree*, so
each arm's gate sits directly under its own selector (adjacent); a two-level
tree-mirrored join folds level by level to `1`. And in the *clean* regime — each
arm computed under its assumed pc, exporting the *constant* `1/1` with no inner
gate — the merge is just $"ite"(c_0, 1, "ite"(c_1, 1, … 1))$, and #ok[one rule],
$"ite"(c, a, a) -> a$, suffices at any depth. The failure shape to avoid is a
*flat* $N$-way select over deep conjunctive flags ($not c_0 and … and c_k$ buried
below other conditions): there the gate is *not* adjacent to a selector, the
context rules cannot reach it, and we are back to the sum.

*Sum regime (linear thread), same match.* The exit chunk is
$"ite"("flag"_0, 1, 0) + "ite"("flag"_1, 1, 0) + …$. `add-sub-cancel` cannot fire
(no subtraction); the context identities cannot fire (no nested `ite`, only a `+`
spine). The proof stalls until `merge_ite_sum` groups the partition — the pass
whose budget and shape-guessing this section flags as fragile.

*Measured.* On the isolated if-else select tower the two context rules turn a
#bad[tier-4 case split] (`prove_tier4: 1`) into #ok[five local rewrites]
(`prove_tier4: 0`), suite still green (292/292). Their cost is why they are not
default-on *yet*: searching every `ite`-bucket class each iteration roughly
*doubles* wall time on the additive-thread benchmarks we run today (#sym.tilde 2 s
$-> #sym.tilde 4$ s on `structs_enums.vpr`), which never produce a select. So they
ship *opt-in* (`SILVER_OXIDE_PRUNE_ITE`) until the heap-join lowering that emits
selects lands — at which point they replace `merge_ite_sum` on that shape with
terminating, local, case-split-free rewriting.

This is the concrete reason the heap-join architecture pays: it emits the *select*
shape, which the pc-free archive collapses with terminating local rules, instead
of the *sum* shape, which forces the one non-local pass. The ground/scratch split
of the previous sections is what makes the select clean — each arm proves under its
own assumed pc and exports a constant, so the join is `ite`-of-constants, not a
gated accumulation.

=== A part-way retrofit: heap ternaries on the linear CFG

The full ground/scratch split is *not* a prerequisite for the select shape. The
same encoding is reachable as an incremental retrofit of the current linear-CFG
lowering, with no block-scoped e-graphs:

- *Fork, don't thread.* Today one running heap is threaded through the topological
  walk and each arm's contribution is *added* onto it, gated to zero off its path
  (`Sink::gate_perm`) — the additive thread that produces the sum. Instead, give
  each block an *entry heap forked from its predecessors' exits*: a heap chosen by a
  `HeapInst::Ternary(cond, then, else)` over the incoming edge conditions, exactly
  the phi that `build_entry_env` already builds for *values*. Each arm then works on
  its own fork, *ungated*, so its permissions are plain amounts — not `ite`-gated
  contributions.
- *Join by select.* At a merge the arms' exit heaps combine into one heap ternary,
  which read *per chunk* is $"ite"("cond", "perm"_"then", "perm"_"else")$. A
  constructed chunk is `1/1` in every arm, so the join is $"ite"("cond", 1, 1) -> 1$
  by the fold already in the rule set; a borrow-return arm cancels to `1/1` inside
  its own fork by `add-sub-cancel`. No additive sum is ever formed — `merge_ite_sum`
  is never invoked.

The IR already carried a `HeapInst::Ternary`; it was removed when the linear
reach-gated thread replaced it. The retrofit re-adds it, plus the verifier step that
distributes a permission/deref lookup through it
($"perm"("loc", "ite"(c, h, h')) = "ite"(c, "perm"("loc", h), "perm"("loc", h'))$),
after which the existing `ite`-reductions and the opt-in context-pruning rules close
the select. Nested branches produce nested heap ternaries that *mirror the branch
tree*, so the per-chunk select is tree-structured and folds locally at any depth.

*An incidental win — address stability.* Forking from the shared pre-split heap
also stabilizes chunk *addresses*: both arms snapshot against the same base, so a
snapshot-derived address (`p_Param(*v)` built from `snap[h]`) is the same e-class in
each arm and the per-chunk join lines up — the instability that otherwise limits the
additive thread.

*The cost it re-incurs.* Heap ternaries make a permission/deref lookup *branch* —
distributing through a nested `ite` of heaps — which is exactly what the linear
thread was introduced to avoid. The trade is deliberate: a branching-but-#ok[local]
lookup that terminating rules collapse, in place of a flat lookup whose permission
is an #bad[AC-hard sum] only a bespoke pass can crack. It does *not* buy the
small-state "forget" benefit of block-scoped graphs — the graph stays monolithic —
so it is purely the sum $->$ select encoding fix, and a stepping stone to the full
architecture, which needs the select regardless.

=== Roles on the graph: target the permission world, escalate by erasing

The `ite` rules of Section 1 are too *general*: they fire on every `ite` in the
graph, though most — control guards, program values — will never be the permission
partition we want to collapse. The graph is polluted with reasoning that cannot help
the obligation at hand, and the rules churn over it. The fix is to give the graph
*roles*.

*A `Perm` world, structurally apart.* A permission amount is a distinct sort —
`Perm`, carrying the same literals as `Real` (`1/1`, `1/2`, `0`) but a separate
world, with its *own* `ite` and arithmetic e-node variants — bridged to the real
world only by explicit, *uninterpreted* $"real" -> "perm"$ / $"perm" -> "real"$
casts. The permission-collapse rules (the select fold, the context-pruning of the
previous section, the partition collapse) are written in the perm world, and because
egg buckets e-nodes by their *operator*, they fire *only* on perm classes. A control
or value `ite` is never even scanned — the targeting is egg's own matching index, at
no search cost, not an applier-side guard.

This is #ok[sound by construction], not by careful guarding: a perm rule *cannot*
match a real node — it is a pattern-level mismatch — so no reasoning leaks across the
boundary, and the cast being uninterpreted means nothing crosses unless a rule
explicitly bridges it. The sort is a soundness-preserving *restriction* of the true
semantics (`Perm` and `Real` are equal underneath); it only ever *narrows* what
fires, never changes a result. Duplicating a handful of arithmetic rules across the
two worlds is the price, and it is small — the generic appliers can be made
parametric over the variant so `ite(c,a,a) -> a` stays single-sourced.

*Two regimes.* We try to discharge the obligation entirely *inside* the perm world,
never crossing a cast — which suffices for the overwhelming majority of Prusti's
permission goals, whose amounts are literal `write`s. A cheap syntactic check routes
the goal: if its cone touches no cast it is a pure-perm goal and the targeted regime
is complete for it; if it does, the goal genuinely relates a permission to a program
value. For that rare crossing we *re-encode into a generic, role-free graph with a
unified encoding*: casts become the identity, the sorted `ite`s collapse back to
plain `ite`s, and the full rule set runs over the merged view. The fast, targeted
regime clears the common case; the general regime is the fallback for the crossing,
and re-encoding is sound exactly because erasing the roles recovers the semantics
they restricted. The re-encode is a *scratch* — a fresh graph with the roles erased,
saturated and discarded — so the role-sorted graph stays the fast, clean working
state.

*The same discipline for path conditions.* Reach and branch booleans are their own
role too, so pc-directed rewrites target only pc classes and never churn the
perm/value fragments — and, conversely, path-condition machinery does not pollute the
graph regions that discharge the simple obligations. Roles partition the graph into
slices, each rule set sees only its slice, and the expensive rules never touch the
fragments that cannot use them. This is the direct answer to Section 1's "rules grew
too general and fire too much": *make them un-general by construction*, and erase the
roles only when a proof genuinely needs the unified view.

Roles are the *targeting* axis; the heap ternaries of the previous section are the
*structural* axis. Structure makes a permission a nested `ite` instead of a sum;
roles make the collapse rules see only that `ite`. They multiply: a perm-typed heap
select is collapsed by perm-world rules alone, at a cost proportional to the perm
fragment, not the whole method.

== The fallback tier, and a strictly-Z3-less mode

When a scratch cannot close a goal it asks Z3 (Section 6). *If Z3 also fails, we
fail* — the goal is genuinely unverified. There is no further tier straining the
e-graph into a full prover; Section 1 is the evidence that road does not pay.

There is one variant. A *strictly Z3-less* mode — fast, useful when a run should
never call an SMT solver — instead *notes the unproved obligation and continues*
as if it held. The noted goals are the honest output: a finite list of what could
not be shown by lightweight means alone. This trades completeness for speed, and
such a note could just as well be emitted as a `VMIR-pure` for another
tool to discharge.

= Blocks: independence buys small state

Making the region a *basic block* turns the two-graph design into an architecture,
and the payoff is *independence between sibling branches*. This is why grounds are
cloned per arm rather than shared. The alternative — one global ground that exports
just the cone visible to each arm — is *not* feasible: it would still couple the
arms, because both an arm's *quantifier instantiations* and any *"global" truths*
it discovers would land in the shared graph and bleed into its siblings. We want a
strong guarantee: *reordering the branches never changes the verification result.*
Clone-on-split and merge-on-join gives exactly that — each arm reasons in its own
copy, sees only what it and its ancestors learned, and the arms meet only at the
join. Quantifier pollution (trigger instantiations from one arm leaking into a
sibling — an unsoundness we currently accept) is fixed by the same construction:
instantiations still travel, but only *forward*, down the block DAG through the
clone/merge structure, never *across* to a sibling.

Independence buys more than soundness. Each block carries only *its own small
state*, so it is fast for the same reason Silicon's per-path Z3 is fast: it
*forgets*. A monolithic graph cannot — the whole-method history is one serial,
ever-growing object that every obligation must walk.

A block also *assumes its path condition once*. Today the pc is folded into every
obligation separately — each `assert` clones a probe graph, unions in
$"pc" #sym.arrow.double "goal"$, and re-saturates it — so a block with $m$
obligations pays $m$ clones and $m$ saturations of essentially the same state. In
a scratch the pc is assumed once at block entry; all $m$ obligations then discharge
against that *single* saturated graph — no per-instruction pc-fold, no re-clones,
no re-saturations. The per-block setup cost is amortized over the whole block
instead of repaid at every instruction.

== The architecture in full

+ *Grounds stay pc-free, always* — each holds its region's facts,
  congruence-compacted, cheap rules plus quantifier instantiation only, no pc
  guards in the terms.

+ *At a split, clone the ground — one copy per arm.* Each arm reasons in its own
  clone and sees only what it and its ancestors learned.

+ *A block's scratch starts as a copy of the current ground, with the block's pc
  assumed.* Inside, the branch's flags and discriminants are known constants rather
  than free booleans, so the goals are discharged against a concrete path.

+ *Discharge in the scratch; on failure ask Z3; if Z3 fails, fail* (or, in Z3-less
  mode, note-and-continue).

+ *On `assume`/`assert`, update the region's ground too* — flat, no pc guard,
  since the clone is already the branch context.

+ *At a join, merge the arms' grounds — and with them the arm heaps.* Since grounds
  carry *no* path condition, this is a union *at the term level* (appendix): the
  arms diverged after the split, so their ids no longer agree — each live value is
  re-added from its arm's extracted term, and a value that genuinely differs by arm
  becomes an `ite` on the arm's reach condition. The heaps merge the same way: both
  arms' chunk sets are re-added and `merge_chunks` consolidates whatever proves equal
  in the merged graph, producing the downstream ground heap. This is the one place
  `merge_chunks` and the permission collapse are still needed, now in a small, fresh
  scope with no cross-method cancellation residue to guess at.

One detail this raises — an e-class id is stable only inside *one* graph, so a value
must be *named* to survive a join or an `old` read — is mechanical, not part of the
core argument: the durable name is the method-global VMIR SSA value, and a join
re-adds the extracted terms it references into the successor graph. A concrete
block-based VMIR and this naming scheme are sketched in the appendix. The one assumption they rest on is *reducible, structured* control flow — a
series-parallel block DAG where every split has a matching join — which
Prusti-from-Rust provides. This is not a limit on branch count: a "cube" of $K$
independent diamonds is still structured, and we join after each diamond rather than
enumerate its $2^K$ paths (exactly the win over Silicon's default). Only genuinely
*irreducible* control flow is excluded, which the target language does not produce.

= Quantifier instantiation stays in egg

Because instantiation is a *strength*, we do *all* of it in the e-graph — functions,
their bodies and postconditions, triggers firing over congruence. This also improves
the fallback: a goal handed to Z3 arrives with the instantiations *already made*, so
the solver starts from a richer state instead of rediscovering the same triggers.

= Z3 integration

Z3 is the single heavier tier below the scratches. The natural wiring is a *Z3 state
that mirrors the ground e-graph*. Keeping the mirror in sync is the real engineering
work: it means *tracking the unions and rewrites* the graph performs and replaying
them into Z3 incrementally, rather than re-encoding from scratch each query. We
think this is doable — *encoding an e-graph into Z3 is not especially hard* (each
e-class an uninterpreted term, each e-node an equation, congruence free in the
solver) — and the incremental delta-sync is the same shape as the ground's own
incremental update. A failing scratch then queries Z3 against a solver already
carrying the ground's facts and egg's instantiations, so the fallback is cheap to
set up even when the goal is hard.

= Reference points and honest risks

The two systems we measure against each embody half of this design. *Silicon with
joins* — its default is exponential on $K$ independent `if`s (#bad[$2^K$ paths],
#sym.tilde 4 min at $K = 16$); `--moreJoins 2` retrofits joins that collapse the same case
to #ok[#sym.tilde 4 s flat]. Block-structured joins are validated inside Silicon
itself, and the thesis evaluation must compare against `--moreJoins`, not the
defaults. *Silicon's per-path Z3* survives our benchmark by native case splits on
the flag partition and by *forgetting* — every query push/pop on one path, no
whole-method state. Our design combines both: block-scoped, discardable scratches for
state and instantiation control, and a synced Z3 tier for the case-split residue.

The open problems are named, not hidden. *Three live representations* — the ground,
a scratch, and the mirrored Z3 state may all exist at once, and the overhead of
keeping all three consistent is unclear; it could eat some of the win the smaller
scratches buy. (*Heap residency* is *not* on this list: the heap rides the graph, so
cloning the ground clones its heap along with it, and a scratch's aggressive merges
are simply never written back — the ground is not *allowed* to merge what only the
branch justifies, so there is nothing to reconcile and no id-remapping bookkeeping.)
*Unbounded ground growth* — the first version does not prune the e-graph, so a long
method's ground grows monotonically; a single method is bounded, but a very large one
could strain memory. Pruning is deferred to Appendix B, with the id-stability care it
implies. *Ground–Z3 sync* rests on faithfully tracking every
union and rewrite. None of these undercut the core claim:
the
present architecture forces the e-graph to prove what it is bad at, pays for it in
`ite`-bloat and a fragile collapse heuristic, and *still* hits a hard ceiling local
tuning has failed to remove (eager consolidation only moved it from 10 to 18 arms).
Store in the ground, prove in the small, fall back to Z3 — that is the principled
endpoint, and we should not push the e-graph past it.

#pagebreak()
#counter(heading).update(0)
#set heading(numbering: "A.1")

= Appendix — block-based VMIR and value naming #text(fill: rgb("#c0392b"))[(WIP)]

#block(fill: rgb("#c0392b").lighten(88%), inset: 0.7em, radius: 3pt, width: 100%)[
  *Work in progress.* This appendix is a rough sketch of one possible block-based
  VMIR, not a settled design — the syntax and the naming details are still moving.
  The core argument (Sections 1–8) does not depend on it.
]

_How blocks are implemented is not part of the core argument; this appendix records
one concrete shape so the claims above have something to stand on._

*Track the ids; the durable name is only for joins.* The normal state is a map from
each live VMIR value — the SSA temp (`v_n` for a pure value, `h_n` for a heap) — to
its `egg::Id`, plus the `Heap` structs, which are themselves just tuples of ids. This
works because *egg ids are append-only stable*: a `union` never invalidates an id (it
canonicalizes, so `find(id)` keeps working), and adding nodes only mints new ids. So
along a *clone-lineage* — ground to scratch, parent block to child — every id ever
minted stays valid, and an ordinary edge carries the id maps forward untouched. No
extraction, no re-add.

*The one discontinuity is a join.* Two sibling arms grow *independently* after the
split, so arm A's `Id(100)` and arm B's `Id(100)` are unrelated for anything added
post-split. This is the *only* place ids do not line up. We reconcile by picking one
arm as the *base graph* and importing the values the join actually references from the
*other* arms — the operands of its `ite`s (below). Each is extracted as a term (a
`RecExpr`, function applications preserved so triggers still fire in the base graph)
and re-added into the base. Everything *ancestral* — defined before the split — has the
*same* id in every arm (all cloned from the split point), so it survives whichever base
we pick, for free; only the handful of values the join names from the non-base arms is
ever re-expressed.

*No explicit live sets are needed.* A block references values by their method-global
SSA id and defines new ones; a join names its predecessors and reconciles exactly the
ids its `ite`s mention — the verifier knows each id's defining block, so it knows which
arm to import from. There is no separate live-in/live-out annotation to maintain.
(Pruning, were it added, would compute its own liveness; see Appendix B.) A name means
the same value in every block; only the `egg::Id` behind it is block-local, and only
across a join.

*A heap is not one term.* What a heap *covers* — how many chunks, at which addresses,
which alias — is a verification-time quantity the IR never stores; a `HeapVal` names
the whole chunk set, resolved at verification time. Along a lineage that costs
nothing (the `Heap` struct of ids is carried as-is); only when a heap is re-expressed
at a join do we walk its chunks and re-add each chunk's `(addr, perm, value)`.

*Phis are just `ite` instructions.* There is no special phi node. A join block names
its predecessors with the reach condition under which each was taken, and then simply
*opens with ordinary `ite` instructions* — one per value that differs across arms:
`v6 := ite(v3, v4, v5)` selects `v4` from the `v3` arm, `v5` from the `!v3` arm. Heaps
are identical: `h3 := ite(v3, h1, h2)` is a plain heap ternary, which `merge_chunks`
then consolidates. These openers are indistinguishable from any other inline ternary
in the IR — the same `PureInst::Ternary` / `HeapInst::Ternary`. A value *identical* in
both arms (ancestral or base-arm) needs no `ite`; it flows straight through keeping its
id. A heap `ite` is well-formed only when the arms' footprints reconcile — today's
"fold on both arms or neither" requirement, not a new obligation, since cross-arm
aliasing is verification-time.

*`old` needs no label and no reconstruction — it is a deref against an earlier heap.*
Every heap version is an SSA name `h_i`, and an old heap always *dominates* its use
(you cannot `old` a sibling's heap), so it is *ancestral*: its chunk ids were minted
upstream and are still valid in the current scratch. `old(e)` is just `e` with its
derefs reading `h_i` instead of the current heap — keep the `Heap` value and deref it,
nothing to rebuild. With pruning deferred, `h_i`'s ids are never dropped, so this is
unconditional; if pruning returns, `h_i` must be kept live down to its last old-use
(Appendix B).

A worked example: read `x.f`, branch on it, write `x.f` on both arms, then at the
join assert the new value exceeds the old — the old value read straight off the entry
heap `h0`, which is simply threaded to the join so it stays addressable there. (Ops
are schematic pseudo-VMIR.)

#block(fill: luma(247), inset: 0.8em, radius: 3pt, width: 100%)[
```
b0:                               // v0 = param x;  h0 = entry heap, acc(x.f, 1/1)
  v1 := addr_f(v0)                // &x.f
  v2 := deref(h0, v1)             // x.f at entry
  v3 := v2 > 0
  branch v3 -> b1, b2

b1:                               // then: x.f := x.f + 1
  v4 := v2 + 1
  h1 := store(h0, v1, v4)         // new heap version
  goto b3

b2:                               // else: x.f := x.f + 2
  v5 := v2 + 2
  h2 := store(h0, v1, v5)
  goto b3

b3 from b1 (v3), b2 (!v3):
  v6 := ite(v3, v4, v5)           // pure phi = ordinary ite over the reach cond
  h3 := ite(v3, h1, h2)           // heap phi = ordinary heap ite; merge_chunks folds it
  v7 := deref(h0, v1)             // old x.f  (old = deref of entry heap h0)
  assert v6 > v7                  // new x.f > old x.f
```
]

No in/out annotations: each block just references values by their method-global id and
defines new ones. The join needs no special phi node either — it opens with plain
`ite`s over the reach condition `v3`, one per value that differs across arms (`v6`,
`h3`), the same `Ternary` the IR uses anywhere; reconciliation imports exactly those
`ite` operands (`v4`/`h1` from `b1`, `v5`/`h2` from `b2`) into the base graph. Ids
increase monotonically and are *never reused*: the two arms take *disjoint* ids even
though only one runs — which is what makes a name method-unique. Note the two roles
`h0` plays: a normal heap value used in `b3`, and being addressable there is what makes
`old(x.f)` = `deref(h0, v1)` — no separate `old` machinery. `v1` and `h0` are ancestral
(same id in both arms), so they need no `ite`, while `v2` — used in the arms but not
past them — is simply never mentioned again.

= Appendix — pruning the e-graph (deferred) #text(fill: rgb("#c0392b"))[(WIP)]

#block(fill: rgb("#c0392b").lighten(88%), inset: 0.7em, radius: 3pt, width: 100%)[
  *Deferred optimization.* The first version does *not* prune the e-graph. This
  appendix records how pruning would work and what it costs in id-stability, for when
  a method's ground grows large enough to need it.
]

*What pruning does.* Even with scratches discarded at block exit, a long method's ground
accumulates intermediate terms no later goal needs. Pruning drops e-nodes and
e-classes no longer reachable from a *live set* of GC roots — the values still
referenced downstream, which pruning would compute by its own liveness pass over the
block DAG (the base design carries no in/out annotation). Two variants: prune at block
boundaries, and prune *mid-block* so a long block is not transiently dominated by nodes
nothing downstream reads. Both are the block principle — *forget what you no longer
need* — at finer grain.

*Two exceptions to reachability.* Reachability from a live value is not the whole
test. A *function application must be kept even when unreachable*: it is a trigger and
can fire a quantifier instantiation at any later point, so dropping it silently loses
facts we might still derive — the same function-application preservation the join's
extract-and-re-add relies on (Appendix A). *Dead quantifier nodes*, by contrast, are
safe to drop: every instantiation is added as an *implication* (guard $#sym.arrow.double$
body), so a trigger node that can no longer fire produces nothing, and its removal
changes no result. Within a surviving class, only *one representative* e-node need be
kept.

*Heaps as roots.* A live heap roots all of its chunks' `addr`, `perm`, and `value`
classes — computed from the heap's verification-time content, not a static list. So a
live heap is a heavier root than a scalar: it pins its chunk cone. It does *not* pin
the whole upstream graph — intermediate temps that fed the computation but are not
part of a live chunk still go.

*Pruning versus `old` — the id-stability care.* This is the cost the first version
avoids. Pruning drops ids, and dropping an id an `old` still needs would break it. The
discipline is a language restriction plus a liveness rule:

- *`old` may refer only to a heap whose definition strictly dominates the use.* This
  is what makes the reference sound even without pruning, and it has a sharp
  consequence for pruning: if `def(h_i)` dominates use `U`, it dominates every split
  between them (otherwise the other arm reaches `U` without `h_i`, contradicting
  dominance), so `h_i` is *ancestral* at every intervening join — same id in both
  arms — and its id is stable along the whole `def`–`U` span.
- *An old-referenced heap is kept live from its definition to its last `old`-use* —
  a heap-shaped live-through value. Pruning then removes everything unreachable from
  ${"current live values"} union {"old-referenced heap versions"}$.

So pruning is not killed by `old`; it is enlarged by exactly the old-referenced heaps,
which is the minimum that must survive to answer those queries — there is no cheaper
representation of an old value, and a heap cannot be re-derived without its state. You
pay only for heaps actually read via `old`; an unreferenced heap version is pruned the
moment nothing else needs it. The bounded, honest cost is a footprint's worth of chunk
cones retained over each `old`-reference's live range.
