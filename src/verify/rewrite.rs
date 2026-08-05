//! Structural egg rewrite rules for the verifier.

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

use egg::{
    Applier, EGraph, Id, PatternAst, Rewrite, SearchMatches, Searcher, Subst, Symbol, Var,
    rewrite as rw,
};

use crate::verify::analysis::ConstFold;
use crate::verify::cert::FunctionDefinition;
use crate::verify::lang::{Discriminant, FuncId, RecipeId, Symbolic};
use crate::verify::quant::RecipeTable;
use crate::vmir::{BinOp, Literal, Polarity, Type, Val};

type Rule = Rewrite<Symbolic, ConstFold>;

fn var(name: &str) -> Var {
    name.parse().expect("valid pattern var")
}

// Applier-memo scoping ("already instantiated this call/σ"). A pure cost guard
// keyed on canonical e-class ids; re-instantiating is idempotent.
//
// - **Live** runs write to a **base** set that survives across runs: the live
//   e-graph of a unit only grows, so an entry stays valid for the whole unit.
// - **Scratch** runs (tier-3 probes, forall-WD checks) saturate a throwaway
//   clone and write to an **overlay** instead. A leaked scratch entry would be a
//   completeness bug: the clone's ids can collide with ids the live graph mints
//   later. Reading the base from a scratch run is fine.
//
// Scopes nest, and a nested clone contains everything its parent's graph does,
// so overlays form a stack: a run reads the base plus every active overlay and
// writes to the top one. A scope's overlay lives as long as its id is on the
// stack — the long-lived per-block scratch `resume`s one id across all of its
// runs so its instances stay remembered (a fresh scope per run measured ~2×
// slower on `structs_enums.vpr`).
//
// All state is thread-local; the `Mutex` in [`Memo`] only satisfies egg's
// `Send + Sync` bounds.
thread_local! {
    /// Bumped per verification unit (`VerifyContext::new`): unit boundaries
    /// switch to a fresh e-graph, so all remembered ids are meaningless.
    static UNIT_GEN: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// The active scratch scopes, innermost last. Each entry is a scope id whose
    /// overlay is readable (and, for the last one, writable). Empty = a live run.
    static SCRATCH_STACK: std::cell::RefCell<Vec<u64>> =
        const { std::cell::RefCell::new(Vec::new()) };
    /// Source of scope ids. Fresh per [`ScratchScope::enter`]; a block scratch
    /// takes one at build time and `resume`s it for each of its runs.
    static NEXT_SCOPE: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Mint a scope id to be `resume`d later — for a scratch graph that outlives a
/// single run (the per-block scratch).
pub(crate) fn new_scope_id() -> u64 {
    NEXT_SCOPE.with(|g| {
        let id = g.get() + 1;
        g.set(id);
        id
    })
}

/// Start a new memo unit. Call when a fresh e-graph is created for a unit.
pub(crate) fn new_memo_unit() {
    UNIT_GEN.with(|g| g.set(g.get() + 1));
}

/// RAII marker for a scratch (throwaway-clone) saturation scope.
pub(crate) struct ScratchScope;

impl ScratchScope {
    /// A one-shot scope: its overlay dies with the returned guard. For throwaway
    /// clones (tier-3 probes, WD checks).
    pub(crate) fn enter() -> Self {
        Self::resume(new_scope_id())
    }

    /// Re-enter the scope `id`, so a graph that outlives one run keeps its memo
    /// across runs. Must nest LIFO with every other scope.
    pub(crate) fn resume(id: u64) -> Self {
        SCRATCH_STACK.with(|s| s.borrow_mut().push(id));
        ScratchScope
    }
}

impl Drop for ScratchScope {
    fn drop(&mut self) {
        SCRATCH_STACK.with(|s| {
            s.borrow_mut().pop();
        });
    }
}

struct MemoInner<K> {
    unit: u64,
    base: HashSet<K>,
    /// One set per active scratch scope, innermost last, tagged with the scope id
    /// it belongs to. Pruned lazily against [`SCRATCH_STACK`] on each insert: a
    /// position whose id no longer matches belongs to a scope that has exited, so
    /// it and everything above it are dropped.
    overlays: Vec<(u64, HashSet<K>)>,
}

/// A unit-scoped applier memo with a scratch overlay (see module docs above).
pub(crate) struct Memo<K>(Mutex<MemoInner<K>>);

impl<K: Eq + std::hash::Hash> Memo<K> {
    fn new() -> Self {
        Self(Mutex::new(MemoInner {
            unit: u64::MAX,
            base: HashSet::new(),
            overlays: Vec::new(),
        }))
    }

    /// `true` when `key` has not been seen in the current scope — the caller
    /// should build the instance. Records the key in the base (live run) or
    /// the overlay (scratch run).
    fn insert(&self, key: K) -> bool {
        let unit = UNIT_GEN.with(|g| g.get());
        let mut memo = self.0.lock().unwrap();
        if memo.unit != unit {
            memo.unit = unit;
            memo.base.clear();
            memo.overlays.clear();
        }
        if memo.base.contains(&key) {
            return false;
        }
        let stack = SCRATCH_STACK.with(|s| s.borrow().clone());
        if stack.is_empty() {
            memo.overlays.clear();
            return memo.base.insert(key);
        }
        // Drop overlays whose scope has exited (id mismatch at its position, or
        // beyond the current depth), keeping the live prefix.
        let keep = stack
            .iter()
            .zip(memo.overlays.iter())
            .take_while(|(id, (oid, _))| *id == oid)
            .count();
        memo.overlays.truncate(keep);
        if memo.overlays.iter().any(|(_, set)| set.contains(&key)) {
            return false;
        }
        // Materialize the remaining active scopes (each nested clone contains
        // everything its parent had, so an empty set for a scope is just "nothing
        // recorded there yet"), then record against the innermost.
        for id in &stack[memo.overlays.len()..] {
            memo.overlays.push((*id, HashSet::new()));
        }
        memo.overlays
            .last_mut()
            .expect("stack non-empty")
            .1
            .insert(key)
    }
}

// ---- Per-rule timing --------------------------------------------------------

thread_local! {
    /// Per-rule search/apply wall clock, accumulated by [`timed`] wrappers and
    /// drained into `VerifyStats` at the end of a run. Thread-local so parallel
    /// tests don't bleed into each other; one verification runs on one thread.
    /// Keyed by the interned rule `Symbol` (Copy) — stringified only at drain.
    static RULE_TIMING: std::cell::RefCell<HashMap<Symbol, RuleTime>> =
        std::cell::RefCell::new(HashMap::new());
}

use crate::verify::stats::RuleTime;

/// Drain the accumulated per-rule timing (resets the sink).
pub(crate) fn take_rule_timing() -> std::collections::BTreeMap<String, RuleTime> {
    RULE_TIMING.with(|t| {
        std::mem::take(&mut *t.borrow_mut())
            .into_iter()
            .map(|(name, time)| (name.as_str().to_string(), time))
            .collect()
    })
}

fn note_time(name: Symbol, search: f64, apply: f64) {
    RULE_TIMING.with(|t| {
        let mut map = t.borrow_mut();
        let entry = map.entry(name).or_default();
        entry.search += search;
        entry.apply += apply;
    });
}

/// Wrap a rule so its searcher/applier report wall-clock time into the
/// thread-local sink. Pure observation — search results and applications are
/// delegated unchanged.
fn timed(rw: Rule) -> Rule {
    let name = rw.name;
    Rewrite::new(
        name,
        TimedSearcher {
            name,
            inner: rw.searcher,
        },
        TimedApplier {
            name,
            inner: rw.applier,
        },
    )
    .expect("wrapping preserves var bindings")
}

struct TimedSearcher {
    name: Symbol,
    inner: Arc<dyn Searcher<Symbolic, ConstFold> + Send + Sync>,
}

impl Searcher<Symbolic, ConstFold> for TimedSearcher {
    fn search_with_limit(
        &self,
        egraph: &EGraph<Symbolic, ConstFold>,
        limit: usize,
    ) -> Vec<SearchMatches<'_, Symbolic>> {
        let start = std::time::Instant::now();
        let out = self.inner.search_with_limit(egraph, limit);
        note_time(self.name, start.elapsed().as_secs_f64(), 0.0);
        out
    }

    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<Symbolic, ConstFold>,
        eclass: Id,
        limit: usize,
    ) -> Option<SearchMatches<'_, Symbolic>> {
        let start = std::time::Instant::now();
        let out = self.inner.search_eclass_with_limit(egraph, eclass, limit);
        note_time(self.name, start.elapsed().as_secs_f64(), 0.0);
        out
    }

    fn vars(&self) -> Vec<Var> {
        self.inner.vars()
    }
}

struct TimedApplier {
    name: Symbol,
    inner: Arc<dyn Applier<Symbolic, ConstFold> + Send + Sync>,
}

impl Applier<Symbolic, ConstFold> for TimedApplier {
    fn apply_matches(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        matches: &[SearchMatches<Symbolic>],
        rule_name: Symbol,
    ) -> Vec<Id> {
        let start = std::time::Instant::now();
        let out = self.inner.apply_matches(egraph, matches, rule_name);
        note_time(self.name, 0.0, start.elapsed().as_secs_f64());
        out
    }

    fn apply_one(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        eclass: Id,
        subst: &Subst,
        searcher_ast: Option<&PatternAst<Symbolic>>,
        rule_name: Symbol,
    ) -> Vec<Id> {
        self.inner
            .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
    }

    fn vars(&self) -> Vec<Var> {
        self.inner.vars()
    }
}

/// The static structural rule set. Per-ADT cons/proj/tag reductions are minted
/// by the registry (`verify::mono`) and appended by `VerifyContext::new`.
pub fn rules() -> Vec<Rule> {
    static_rules().into_iter().filter(kept).map(timed).collect()
}

/// Ablation gate: `SILVER_OXIDE_DROP_RULES=name1,name2` removes those rules from
/// the saturation and reduction sets. Dropping a rewrite is incomplete, never
/// unsound.
fn kept(rule: &Rule) -> bool {
    use std::sync::OnceLock;
    static DROP: OnceLock<HashSet<String>> = OnceLock::new();
    let drop = DROP.get_or_init(|| {
        std::env::var("SILVER_OXIDE_DROP_RULES")
            .unwrap_or_default()
            .split(',')
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .collect()
    });
    drop.is_empty() || !drop.contains(rule.name.as_str())
}

/// The terminating structural reductions used to **normalize** the e-graph after
/// heap-producing ops (`fold`/`unfold`). The registry's ADT reductions are
/// appended by `VerifyContext::new`. Kept separate from [`rules`] so that
/// *non-terminating* rules run only during full saturation.
pub fn reduce_rules() -> Vec<Rule> {
    terminating_ite_rules()
        .into_iter()
        .filter(kept)
        .map(timed)
        .collect()
}

/// Build the projection reduction `accessor(ctor(a0..an)) ⇒ a_index` for a
/// single member id, including ones minted after `VerifyContext` construction
/// (monomorphic Option instances).
pub fn proj_rule(accessor: FuncId, ctor: FuncId, index: usize) -> Rule {
    timed(
        Rewrite::new(
            format!("proj-{}", accessor.0),
            UnaryAppSearcher { func: accessor },
            ProjApplier { ctor, index },
        )
        .expect("valid proj rewrite"),
    )
}

/// Build the injectivity rule for one constructor: an e-class holding two
/// applications of the same constructor unions their arguments pairwise
/// (`C(a..) ≡ C(b..) ⟹ aᵢ ≡ bᵢ`). Sound because ADT constructors are free.
///
/// Congruence runs only *forward*, and [`proj_rule`] recovers the backward
/// direction only where a `projᵢ` application exists. Two constructor terms can
/// land in one class with no projection over them, and then the component
/// equalities are reachable only through this rule.
pub fn inj_rule(ctor: FuncId) -> Rule {
    timed(
        Rewrite::new(
            format!("inj-{}", ctor.0),
            AxiomTriggerSearcher { func: ctor },
            InjApplier { ctor },
        )
        .expect("valid injectivity rewrite"),
    )
}

/// Build the discriminator reduction `tag_fn(ctor_C(..)) ⇒ index_C` for a single
/// (possibly synthesised) tag function. Companion to [`proj_rule`].
pub fn tag_rule(tag_fn: FuncId, ctor_tags: HashMap<FuncId, usize>) -> Rule {
    timed(
        Rewrite::new(
            format!("tag-{}", tag_fn.0),
            UnaryAppSearcher { func: tag_fn },
            TagApplier { ctor_tags },
        )
        .expect("valid tag rewrite"),
    )
}

/// The static (ADT-independent) rule set run during saturation.
fn static_rules() -> Vec<Rule> {
    let mut rules = terminating_ite_rules();
    rules.extend(vec![
        // Arithmetic identities, written once per operand sort (`+i` / `+r`) so
        // that a rule producing a literal produces the right one: an integer `0`
        // and a permission `0/1` are different literals, and merging them into
        // one e-class is a type error the analysis panics on.
        //
        // x + 0 => x
        rw!("add-zero-int-r"; "(+i ?x 0)" => "?x"),
        rw!("add-zero-int-l"; "(+i 0 ?x)" => "?x"),
        rw!("add-zero-real-r"; "(+r ?x 0/1)" => "?x"),
        rw!("add-zero-real-l"; "(+r 0/1 ?x)" => "?x"),
        // x - 0 => x
        rw!("sub-zero-int"; "(-i ?x 0)" => "?x"),
        rw!("sub-zero-real"; "(-r ?x 0/1)" => "?x"),
        // x * 1 => x
        rw!("mul-one-real-r"; "(*r ?x 1/1)" => "?x"),
        rw!("mul-one-real-l"; "(*r 1/1 ?x)" => "?x"),
        rw!("mul-one-int-r"; "(*i ?x 1)" => "?x"),
        rw!("mul-one-int-l"; "(*i 1 ?x)" => "?x"),
        // x * 0 => 0
        rw!("mul-zero-real-r"; "(*r ?x 0/1)" => "0/1"),
        rw!("mul-zero-real-l"; "(*r 0/1 ?x)" => "0/1"),
        rw!("mul-zero-int-r"; "(*i ?x 0)" => "0"),
        rw!("mul-zero-int-l"; "(*i 0 ?x)" => "0"),
        // x / 1 => x. No `x / x => 1` or `0 / x => 0`: division by zero is
        // unspecified (see `eval_binary`), so neither holds at `x = 0`.
        rw!("div-one-real"; "(/r ?x 1/1)" => "?x"),
        rw!("div-one-int"; "(/i ?x 1)" => "?x"),
        // (x - p) + p => x, and mirrors. A consume/produce cycle at one location
        // leaves the chunk's permission in this shape. Both operand orders are
        // spelled out because there is no commutativity rule (it blows the graph
        // up).
        rw!("add-sub-cancel-int-r"; "(+i (-i ?x ?p) ?p)" => "?x"),
        rw!("add-sub-cancel-int-l"; "(+i ?p (-i ?x ?p))" => "?x"),
        rw!("add-sub-cancel-real-r"; "(+r (-r ?x ?p) ?p)" => "?x"),
        rw!("add-sub-cancel-real-l"; "(+r ?p (-r ?x ?p))" => "?x"),
        rw!("sub-add-cancel-int-r"; "(-i (+i ?x ?p) ?p)" => "?x"),
        rw!("sub-add-cancel-int-l"; "(-i (+i ?p ?x) ?p)" => "?x"),
        rw!("sub-add-cancel-real-r"; "(-r (+r ?x ?p) ?p)" => "?x"),
        rw!("sub-add-cancel-real-l"; "(-r (+r ?p ?x) ?p)" => "?x"),
        // x - x => 0. The cancel rules above need nested `-`/`+` and so miss a
        // bare self-subtraction, which is what a give-back leaves when the
        // returned share is not the outer addend (`(p - p) + 1/1`).
        rw!("sub-self-int"; "(-i ?x ?x)" => "0"),
        rw!("sub-self-real"; "(-r ?x ?x)" => "0/1"),
        // x < x => false   (irreflexivity)
        rw!("lt-irrefl-real"; "(<r ?x ?x)" => "false"),
        rw!("lt-irrefl-int"; "(<i ?x ?x)" => "false"),
        // x == x => true   (reflexivity; also fires once congruence has merged
        // the two operands into one e-class)
        rw!("eq-refl"; "(== ?x ?x)" => "true"),
        // (a == b) proven true  =>  a ≡ b   (congruence)
        rw!("eq-true-union"; "(== ?a ?b)" => {
            UnionEqArgs { a: var("?a"), b: var("?b") }
        }),
        // `b == false` is `!b`, which lowers to `ite(b, false, true)`
        // (`translate/pure_exp.rs`, `UnOp::Not`). An equivalence, so no `Known`
        // gate. Load-bearing for splitting: `split_candidates` only collects
        // `Ite` conditions, so a goal left in the `== false` spelling (how Prusti
        // emits MIR asserts) offers the splitter nothing.
        rw!("eq-false-is-not-r"; "(== ?b false)" => "(ite ?b false true)"),
        rw!("eq-false-is-not-l"; "(== false ?b)" => "(ite ?b false true)"),
        // `b == true` is `b` itself — a pure union, minting no node.
        rw!("eq-true-is-self-r"; "(== ?b true)" => "?b"),
        rw!("eq-true-is-self-l"; "(== true ?b)" => "?b"),
        // The boolean decompositions (and-true, or-false, not-true) live in the
        // fused `ite-reduce` pass — they are `Ite`-bucket shapes conditioned on
        // the class's proven boolean, exactly what its applier already inspects.
    ]);
    // Disequality reasoning over disproven `==` classes — standalone rules that
    // share the `Eq` bucket + the `Known(false)` gate.
    rules.push(
        Rewrite::new("eq-false-mirror", EqBucketSearcher, EqFalseMirrorApplier)
            .expect("eq-false-mirror rule"),
    );
    rules.push(
        Rewrite::new(
            "contra-congruence",
            EqBucketSearcher,
            ContraCongruenceApplier { memo: Memo::new() },
        )
        .expect("contra-congruence rule"),
    );
    rules.extend(disequality_unit_prop_rules());
    rules
}

/// Unit propagation from a **disproven** `==` through `ite` towers — NOT
/// eq-over-ite distribution (see the applier doc). Split by which arm the other
/// operand matches; nested towers unwind one level per saturation iteration (the
/// derived disequality re-enters the `Eq` bucket).
fn disequality_unit_prop_rules() -> Vec<Rule> {
    vec![
        Rewrite::new(
            "eq-false-then",
            EqBucketSearcher,
            EqFalseUnitApplier {
                then_side: true,
                memo: Memo::new(),
            },
        )
        .expect("eq-false-then rule"),
        Rewrite::new(
            "eq-false-else",
            EqBucketSearcher,
            EqFalseUnitApplier {
                then_side: false,
                memo: Memo::new(),
            },
        )
        .expect("eq-false-else rule"),
    ]
}

/// Terminating `ite` simplifications, shared by the saturation rule set and the
/// post-`fold`/`unfold` reduction set. Under an assumed branch literal these
/// reduce a gated permission `b ? p : 0` to `p` (resp. `0`).
///
/// Fused into **one** rule that scans the `Ite` op bucket once per iteration and
/// node-checks every shape: as twelve `rw!` patterns they cost ~70% of all search
/// time, since the nested two-level patterns pay a backtracking cross-product
/// over a bucket holding thousands of classes. The fused pass is linear in the
/// bucket (plus the two branch classes' nodes) and union-only.
///
/// Shapes (c ⋄ t ⋄ e over one node, plus one nested level):
/// - `ite(true, x, y) ⇒ x`, `ite(false, x, y) ⇒ y` (via `ConstFold` on `c`)
/// - `ite(c, x, x) ⇒ x`
/// - `ite(c, true, false) ⇒ c`
/// - `ite(c, c, false) ⇒ c`, `ite(c, true, c) ⇒ c`
/// - `ite(c, c, true) ⇒ true`, `ite(c, false, c) ⇒ false`
/// - `ite(c, ite(c, x, y), x) ⇒ x`, `ite(c, x, ite(c, y, x)) ⇒ x`
/// - `ite(c, ite(c, x, y), y) ⇒ ite(c, x, y)`, `ite(c, x, ite(c, x, y)) ⇒ ite(c, x, y)`
fn terminating_ite_rules() -> Vec<Rule> {
    vec![Rewrite::new("ite-reduce", IteBucketSearcher, IteReduceApplier).expect("ite rule")]
}

/// Searcher for the fused ite rule: every e-class holding an `Ite` node, via
/// the `classes_by_op` bucket (no whole-graph scan). One empty subst per class;
/// the applier re-reads the nodes.
struct IteBucketSearcher;

impl Searcher<Symbolic, ConstFold> for IteBucketSearcher {
    fn search_with_limit(
        &self,
        egraph: &EGraph<Symbolic, ConstFold>,
        limit: usize,
    ) -> Vec<SearchMatches<'_, Symbolic>> {
        let Some(classes) = egraph.classes_for_op(&Discriminant::Ite) else {
            return vec![];
        };
        classes
            .take(limit)
            .map(|eclass| SearchMatches {
                eclass,
                substs: vec![Subst::default()],
                ast: None,
            })
            .collect()
    }

    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<Symbolic, ConstFold>,
        eclass: Id,
        _limit: usize,
    ) -> Option<SearchMatches<'_, Symbolic>> {
        egraph[eclass]
            .nodes
            .iter()
            .any(|n| matches!(n, Symbolic::Ite(..)))
            .then(|| SearchMatches {
                eclass,
                substs: vec![Subst::default()],
                ast: None,
            })
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// Searcher for the guarded eq-over-ite distribution: every e-class holding an
/// `Eq` node, via the `classes_by_op` bucket (no whole-graph scan). One empty
/// subst per class; the applier re-reads the nodes.
struct EqBucketSearcher;

impl Searcher<Symbolic, ConstFold> for EqBucketSearcher {
    fn search_with_limit(
        &self,
        egraph: &EGraph<Symbolic, ConstFold>,
        limit: usize,
    ) -> Vec<SearchMatches<'_, Symbolic>> {
        let Some(classes) = egraph.classes_for_op(&Discriminant::Binary(BinOp::Eq)) else {
            return vec![];
        };
        classes
            .take(limit)
            .map(|eclass| SearchMatches {
                eclass,
                substs: vec![Subst::default()],
                ast: None,
            })
            .collect()
    }

    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<Symbolic, ConstFold>,
        eclass: Id,
        _limit: usize,
    ) -> Option<SearchMatches<'_, Symbolic>> {
        egraph[eclass]
            .nodes
            .iter()
            .any(|n| matches!(n, Symbolic::Binary(BinOp::Eq, _)))
            .then(|| SearchMatches {
                eclass,
                substs: vec![Subst::default()],
                ast: None,
            })
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// Applier for `eq-false-mirror`: **disequality symmetry**. A disproven
/// `a == b` implies the mirrored `b == a` is false too — land it in the same
/// class so a goal built in the other operand order sees the known boolean.
/// Proven equalities need no mirror — `eq-true-union` merges the args and
/// congruence collapses both orders.
struct EqFalseMirrorApplier;

impl Applier<Symbolic, ConstFold> for EqFalseMirrorApplier {
    fn apply_one(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        eclass: Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<Symbolic>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        if known_bool(egraph, eclass) != Some(false) {
            return vec![];
        }
        let mirrors: Vec<[Id; 2]> = egraph[eclass]
            .nodes
            .iter()
            .filter_map(|n| match n {
                Symbolic::Binary(BinOp::Eq, [l, r]) if l != r => Some([*r, *l]),
                _ => None,
            })
            .collect();
        let mut changed = Vec::new();
        for [r, l] in mirrors {
            let mirrored = egraph.add(Symbolic::Binary(BinOp::Eq, [r, l]));
            if egraph.union(eclass, mirrored) {
                changed.push(egraph.find(eclass));
            }
        }
        changed
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// Applier for `contra-congruence`: **narrowing contrapositive congruence**.
/// Congruence gives `a⃗ ≡ b⃗ ⟹ f(a⃗) ≡ f(b⃗)`; its contrapositive, from a
/// *disproven* `f(a⃗) == f(b⃗)` with `f` **n-ary**, is the disjunction
/// `a₁≠b₁ ∨ … ∨ aₙ≠bₙ`. An e-graph cannot hold a disjunction of disequalities
/// (it would have to case-split on *which* argument differs — the true/false
/// asymmetry), so we fire **only when the disjunction collapses to a unit**:
/// when every argument pair but one is already proven equal (`aᵢ ≡ bᵢ`), the
/// lone remaining pair must differ — `aⱼ == bⱼ` is false. Sound for **any** `f`,
/// injective or not; unlike [`inj_rule`] the contrapositive of congruence needs
/// no free constructor.
///
/// Connects an unboxed comparison to its boxed source: `value(v) != 0` with the
/// axiom instance `value(cons(0)) ≡ 0` in `0`'s class disproves `v == cons(0)`,
/// which then feeds `eq-false-then/else`'s ite unit propagation and collapses
/// predicate-body disjunction towers via `ite-reduce`.
struct ContraCongruenceApplier {
    /// Cost guard, keyed by the function and the canonical argument pair it
    /// disproved (re-deriving is idempotent — the unions no-op).
    memo: Memo<(FuncId, [Id; 2])>,
}

impl Applier<Symbolic, ConstFold> for ContraCongruenceApplier {
    fn apply_one(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        eclass: Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<Symbolic>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        if known_bool(egraph, eclass) != Some(false) {
            return vec![];
        }
        let mut contras: Vec<[Id; 2]> = Vec::new();
        for node in &egraph[eclass].nodes {
            let Symbolic::Binary(BinOp::Eq, [l, r]) = node else {
                continue;
            };
            let (l, r) = (egraph.find(*l), egraph.find(*r));
            for lapp in &egraph[l].nodes {
                let Symbolic::FuncApp(lf, ltys, largs) = lapp else {
                    continue;
                };
                for rapp in &egraph[r].nodes {
                    let Symbolic::FuncApp(rf, rtys, rargs) = rapp else {
                        continue;
                    };
                    if lf != rf || ltys != rtys || largs.len() != rargs.len() {
                        continue;
                    }
                    // Narrowing: collect the argument positions not yet proven
                    // equal. Exactly one differing ⟹ the disjunction is a unit and
                    // that pair is disequal. Zero means the apps are congruent
                    // (`ConstFold` handles the conflict); two or more is a
                    // disjunction the e-graph cannot represent, so skip.
                    let mut diff: Option<[Id; 2]> = None;
                    let mut multiple = false;
                    for (la, ra) in largs.iter().zip(rargs.iter()) {
                        let (a, b) = (egraph.find(*la), egraph.find(*ra));
                        if a != b {
                            if diff.is_some() {
                                multiple = true;
                                break;
                            }
                            diff = Some([a, b]);
                        }
                    }
                    if let (false, Some([a, b])) = (multiple, diff)
                        && self.memo.insert((*lf, [a, b]))
                    {
                        contras.push([a, b]);
                    }
                }
            }
        }
        let mut changed = Vec::new();
        for [a, b] in contras {
            let eq = egraph.add(Symbolic::Binary(BinOp::Eq, [a, b]));
            let false_ = egraph.add(Symbolic::Lit(Literal::Bool(false)));
            if egraph.union(eq, false_) {
                changed.push(egraph.find(eq));
            }
        }
        changed
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// Applier for `eq-false-then`/`eq-false-else`: **unit propagation through an
/// `ite` operand** of a **disproven** equality. From `(ite c x y) == z` proven
/// `false` (an assumed `d != tag`) with one arm already equal to `z`:
///
/// - `then_side` (`x ≡ z`) ⟹ `c = false` (taking the true branch would
///   satisfy the equality) `∧ (y == z) = false` (the value is the false
///   branch's)
/// - else side (`y ≡ z`) ⟹ `c = true ∧ (x == z) = false` (mirrored)
///
/// The second consequence recurses down a nested ite tower (a 3+-variant enum
/// discriminator): the derived disequality lands back in the `Eq` bucket, so the
/// next saturation iteration picks it up, one level per iteration. Two assumed
/// disequalities pinning `c` both ways make the graph inconsistent — which is
/// enum-match exhaustiveness.
///
/// Deliberately **not** syntactic distribution
/// (`(ite c x y) == z ⇒ ite c (x==z) (y==z)`): the pattern form cross-multiplies
/// the ite guard towers `implication()` builds (~75x node blowup). This
/// derivation adds at most one `Eq` node per step and otherwise only unions.
struct EqFalseUnitApplier {
    /// Which arm of the ite the other operand must match (see rule doc).
    then_side: bool,
    /// Cost guard: one derivation per canonical `[c, x, y, z]` quadruple
    /// (re-deriving is idempotent — the unions no-op).
    memo: Memo<[Id; 4]>,
}

impl Applier<Symbolic, ConstFold> for EqFalseUnitApplier {
    fn apply_one(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        eclass: Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<Symbolic>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        if known_bool(egraph, eclass) != Some(false) {
            return vec![];
        }
        // Each derivation: pin `cond` to `cond_val`, and disprove the other
        // arm's comparison `other == z`.
        let mut derivs: Vec<(Id, bool, Id, Id)> = Vec::new();
        for node in &egraph[eclass].nodes {
            let Symbolic::Binary(BinOp::Eq, [l, r]) = node else {
                continue;
            };
            for (ite_side, z) in [(*l, *r), (*r, *l)] {
                let (ite_side, z) = (egraph.find(ite_side), egraph.find(z));
                for inner in &egraph[ite_side].nodes {
                    let Symbolic::Ite([c, x, y]) = inner else {
                        continue;
                    };
                    let (c, x, y) = (egraph.find(*c), egraph.find(*x), egraph.find(*y));
                    let (matched, cond_val, other) = if self.then_side {
                        (x == z, false, y)
                    } else {
                        (y == z, true, x)
                    };
                    if !matched || !self.memo.insert([c, x, y, z]) {
                        continue;
                    }
                    derivs.push((c, cond_val, other, z));
                }
            }
        }
        let mut changed = Vec::new();
        for (cond, cond_val, other, z) in derivs {
            let lit = egraph.add(Symbolic::Lit(Literal::Bool(cond_val)));
            if egraph.union(cond, lit) {
                changed.push(egraph.find(cond));
            }
            let other_eq = egraph.add(Symbolic::Binary(BinOp::Eq, [other, z]));
            let false_ = egraph.add(Symbolic::Lit(Literal::Bool(false)));
            if egraph.union(other_eq, false_) {
                changed.push(egraph.find(other_eq));
            }
        }
        changed
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// The known boolean of a class, per `ConstFold`. Subsumes matching a literal
/// node (the analysis is seeded by literals), so this fires at least wherever
/// the old `true`/`false` patterns did.
fn known_bool(egraph: &EGraph<Symbolic, ConstFold>, class: Id) -> Option<bool> {
    match egraph[class].data.known() {
        Some(Literal::Bool(b)) => Some(*b),
        _ => None,
    }
}

struct IteReduceApplier;

/// Measurement gate for the two nested same-condition `ite` shapes
/// (`ite(c, ite(c, x, y), _)` and its mirror). Set `SILVER_OXIDE_NO_NESTED_ITE=1`
/// to drop them and cost out the nested branch-class scan.
fn nested_ite_shapes_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SILVER_OXIDE_NO_NESTED_ITE").is_none())
}

impl Applier<Symbolic, ConstFold> for IteReduceApplier {
    fn apply_one(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        eclass: Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<Symbolic>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        // Collect the unions first: node inspection needs `&egraph`.
        enum Target {
            Class(Id),
            True,
            False,
        }
        let mut unions: Vec<(Id, Target)> = Vec::new();
        let self_lit = known_bool(egraph, eclass);
        for node in &egraph[eclass].nodes {
            let Symbolic::Ite([c, t, e]) = node else {
                continue;
            };
            let (c, t, e) = (egraph.find(*c), egraph.find(*t), egraph.find(*e));
            let (t_lit, e_lit) = (known_bool(egraph, t), known_bool(egraph, e));
            // Decompositions: the *class's* proven boolean constrains the parts.
            match self_lit {
                // (a && b) proven true => a, b each true.  a && b is a ? b : false.
                Some(true) if e_lit == Some(false) => {
                    unions.push((c, Target::True));
                    unions.push((t, Target::True));
                }
                // (!x) proven true => x false.  !x is x ? false : true.
                Some(true) if t_lit == Some(false) && e_lit == Some(true) => {
                    unions.push((c, Target::False));
                }
                // (!x) proven false => x true.  Mirror of the arm above; this is
                // how Prusti spells a taken branch (`switchInt` emits
                // `if (value(t) == false) { else } else { then }`, so the arm where
                // the guard holds sits under a negation proven false).
                Some(false) if t_lit == Some(false) && e_lit == Some(true) => {
                    unions.push((c, Target::True));
                }
                // (a || b) proven false => a, b each false.  a || b is a ? true : b.
                Some(false) if t_lit == Some(true) => {
                    unions.push((c, Target::False));
                    unions.push((e, Target::False));
                }
                _ => {}
            }
            match known_bool(egraph, c) {
                // ite(true, x, y) => x
                Some(true) => unions.push((eclass, Target::Class(t))),
                // ite(false, x, y) => y
                Some(false) => unions.push((eclass, Target::Class(e))),
                None => {}
            }
            // c ? x : x => x
            if t == e {
                unions.push((eclass, Target::Class(t)));
            }
            // c ? true : false => c
            if t_lit == Some(true) && e_lit == Some(false) {
                unions.push((eclass, Target::Class(c)));
            }
            // c ? c : false => c  (b && b)
            if t == c && e_lit == Some(false) {
                unions.push((eclass, Target::Class(c)));
            }
            // c ? true : c => c  (b || b)
            if t_lit == Some(true) && e == c {
                unions.push((eclass, Target::Class(c)));
            }
            // c ? c : true => true
            if t == c && e_lit == Some(true) {
                unions.push((eclass, Target::True));
            }
            // c ? false : c => false
            if t_lit == Some(false) && e == c {
                unions.push((eclass, Target::False));
            }
            // Nested same-condition ite in one branch — `c ? (c ? x : y) : e` and
            // its mirror. Every arm collapses the whole class, so the first hit
            // makes any further match redundant: stop on the first collapse and
            // skip the else-branch scan if the then-branch produced one.
            let mut collapsed = false;
            // Large branch classes (the `true` class alone reaches ~1600 nodes on
            // enum-match) almost never hold an inner ite on the same `c`, so
            // scanning them per outer-ite per iteration was 55% of runtime. Skip
            // them — the load-bearing structural-join shape keeps its branch
            // classes tiny, and skipping a rewrite is incomplete, not unsound.
            const NESTED_SCAN_BOUND: usize = 64;
            let nested = nested_ite_shapes_enabled();
            let scan_t = nested && egraph[t].nodes.len() <= NESTED_SCAN_BOUND;
            let scan_e = nested && egraph[e].nodes.len() <= NESTED_SCAN_BOUND;
            //   c ? (c ? x : y) : e
            for inner in scan_t.then(|| &egraph[t].nodes).into_iter().flatten() {
                let Symbolic::Ite([c2, x, y]) = inner else {
                    continue;
                };
                if egraph.find(*c2) != c {
                    continue;
                }
                // c ? (c ? x : y) : x => x
                if egraph.find(*x) == e {
                    unions.push((eclass, Target::Class(e)));
                    collapsed = true;
                    break;
                }
                // c ? (c ? x : y) : y => c ? x : y
                if egraph.find(*y) == e {
                    unions.push((eclass, Target::Class(t)));
                    collapsed = true;
                    break;
                }
            }
            // Nested same-condition ite in the false branch:
            //   c ? t : (c ? x : y)
            if !collapsed && scan_e {
                for inner in &egraph[e].nodes {
                    let Symbolic::Ite([c2, x, y]) = inner else {
                        continue;
                    };
                    if egraph.find(*c2) != c {
                        continue;
                    }
                    // c ? x : (c ? y : x) => x
                    if egraph.find(*y) == t {
                        unions.push((eclass, Target::Class(t)));
                        break;
                    }
                    // c ? x : (c ? x : y) => c ? x : y
                    if egraph.find(*x) == t {
                        unions.push((eclass, Target::Class(e)));
                        break;
                    }
                }
            }
        }

        let mut changed = Vec::new();
        for (source, target) in unions {
            let target = match target {
                Target::Class(id) => id,
                Target::True => egraph.add(Symbolic::Lit(Literal::Bool(true))),
                Target::False => egraph.add(Symbolic::Lit(Literal::Bool(false))),
            };
            if egraph.union(source, target) {
                changed.push(egraph.find(source));
            }
        }
        changed
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// Applier for `eq-true-union`: when a matched `Eq` e-class is proven `true`,
/// union its two argument e-classes. Sound (proven `a == b` ⇒ same value) and
/// size-non-increasing (only merges existing e-classes, never adds nodes).
struct UnionEqArgs {
    a: Var,
    b: Var,
}

impl Applier<Symbolic, ConstFold> for UnionEqArgs {
    fn apply_one(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<Symbolic>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        // Only fire once the equality is actually known true. `Assume` seeds
        // this by unioning the `Eq` e-class with `Lit(true)`, which
        // `ConstFold` records as `Data::Known(Bool(true))`.
        if !matches!(egraph[eclass].data.known(), Some(Literal::Bool(true))) {
            return vec![];
        }
        let a = subst[self.a];
        let b = subst[self.b];
        if egraph.union(a, b) {
            vec![egraph.find(a)]
        } else {
            vec![]
        }
    }

    fn vars(&self) -> Vec<Var> {
        vec![self.a, self.b]
    }
}

/// The pattern variable bound to a tag call's argument.
fn tag_x() -> Var {
    var("?x")
}

/// Searcher for a unary application `func(base)`: matches any `FuncApp(func, _,
/// [base])` node (its ground type args live in the discriminant and are ignored
/// here) and binds `?x` to the single value arg. FuncApp isn't string-matchable,
/// so this is hand-written. Shared by the tag and projection reductions.
struct UnaryAppSearcher {
    func: FuncId,
}

impl Searcher<Symbolic, ConstFold> for UnaryAppSearcher {
    /// Seed only from the e-classes that contain a node with this concept's
    /// operator (egg's `classes_by_op` op-index), instead of egg's default
    /// whole-e-graph scan. Sound because the ground type instantiation is **not**
    /// in the discriminant (it lives in the enode payload), so a single
    /// `Discriminant::FuncApp(func)` bucket holds every instantiation of `func`.
    fn search_with_limit(
        &self,
        egraph: &EGraph<Symbolic, ConstFold>,
        limit: usize,
    ) -> Vec<SearchMatches<'_, Symbolic>> {
        let Some(ids) = egraph.classes_for_op(&Discriminant::FuncApp(self.func)) else {
            return vec![];
        };
        let mut ms = Vec::new();
        let mut limit = limit;
        for eclass in ids {
            if limit == 0 {
                break;
            }
            if let Some(m) = self.search_eclass_with_limit(egraph, eclass, limit) {
                limit -= m.substs.len();
                ms.push(m);
            }
        }
        ms
    }

    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<Symbolic, ConstFold>,
        eclass: Id,
        limit: usize,
    ) -> Option<SearchMatches<'_, Symbolic>> {
        let mut substs = Vec::new();
        for node in &egraph[eclass].nodes {
            if let Symbolic::FuncApp(f, _, args) = node
                && *f == self.func
                && args.len() == 1
            {
                let mut subst = Subst::default();
                subst.insert(tag_x(), args[0]);
                substs.push(subst);
                if substs.len() >= limit {
                    break;
                }
            }
        }
        if substs.is_empty() {
            None
        } else {
            Some(SearchMatches {
                eclass,
                substs,
                ast: None,
            })
        }
    }

    fn vars(&self) -> Vec<Var> {
        vec![tag_x()]
    }
}

/// Applier for the tag reduction: if the argument's e-class holds a constructor
/// of this ADT, union the `tag(..)` e-class with the constructor's tag literal.
struct TagApplier {
    ctor_tags: HashMap<FuncId, usize>,
}

impl Applier<Symbolic, ConstFold> for TagApplier {
    fn apply_one(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<Symbolic>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let xc = egraph.find(subst[tag_x()]);
        let mut tag = None;
        for node in &egraph[xc].nodes {
            if let Symbolic::FuncApp(c, _, _) = node
                && let Some(&t) = self.ctor_tags.get(c)
            {
                tag = Some(t);
                break;
            }
        }
        let Some(t) = tag else { return vec![] };
        let lit = egraph.add(Symbolic::Lit(Literal::Int(num::BigInt::from(t))));
        if egraph.union(eclass, lit) {
            vec![egraph.find(eclass)]
        } else {
            vec![]
        }
    }

    fn vars(&self) -> Vec<Var> {
        vec![tag_x()]
    }
}

/// Applier for [`inj_rule`]: unions the arguments of every pair of same-ctor
/// applications sharing the matched e-class. Grouped by type args — two
/// instantiations of a generic constructor are different operators, and only
/// same-operator applications are congruent.
struct InjApplier {
    ctor: FuncId,
}

impl Applier<Symbolic, ConstFold> for InjApplier {
    fn apply_one(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        eclass: Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<Symbolic>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        // One representative application per type instantiation; every later one
        // is unioned against it argument-wise (transitivity covers the rest).
        let mut reps: Vec<(Box<[Type]>, Box<[Id]>)> = Vec::new();
        let mut pairs: Vec<(Id, Id)> = Vec::new();
        for node in &egraph[eclass].nodes {
            let Symbolic::FuncApp(f, tys, args) = node else {
                continue;
            };
            if *f != self.ctor {
                continue;
            }
            match reps.iter().find(|(t, _)| t == tys) {
                Some((_, rep)) => pairs.extend(rep.iter().copied().zip(args.iter().copied())),
                None => reps.push((tys.clone(), args.clone())),
            }
        }
        let mut changed = Vec::new();
        for (a, b) in pairs {
            if egraph.union(a, b) {
                changed.push(egraph.find(a));
            }
        }
        changed
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// Applier for the projection reduction: if the argument's e-class holds the
/// matching constructor `ctor`, union the `accessor(..)` e-class with that
/// constructor's `index`-th value argument. (Type args are not children, so the
/// value args start at 0.)
struct ProjApplier {
    ctor: FuncId,
    index: usize,
}

impl ProjApplier {
    /// Extract the projected field out of `class`, returning the e-class of the
    /// result (adding `ite` nodes as needed). Either the ctor is directly present
    /// (return the field arg), or the class holds an `ite` whose both arms extract
    /// recursively — the projection commutes into the `ite`
    /// (`projᵢ(ite(c, cons(a..), cons(b..))) ⇒ ite(c, aᵢ, bᵢ)`). The commuting arm
    /// connects an enum discriminator's boxed `ite` body to a switch comparing the
    /// *unboxed* value; without it `proj∘cons` never fires, since the arg class
    /// holds an `Ite` rather than the ctor.
    ///
    /// The argument class is frequently a **shared** `ite`-DAG, so `memo` caches
    /// the per-class result — otherwise a DAG with `d` shared classes is walked
    /// over up to `2^d` distinct paths. `seen` is the in-progress cycle guard: a
    /// class whose extraction depends on an active cycle is *not* memoized (its
    /// `acyclic` return is `false`).
    ///
    /// Returns `(result, acyclic)`: `result` is the extracted class (or `None` if
    /// not projectable); `acyclic` is `false` iff the computation short-circuited
    /// on an in-progress class, marking the result as not cacheable by callers.
    fn project(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        class: Id,
        memo: &mut HashMap<Id, Option<Id>>,
        seen: &mut Vec<Id>,
    ) -> (Option<Id>, bool) {
        let class = egraph.find(class);
        if let Some(&r) = memo.get(&class) {
            return (r, true);
        }
        if seen.contains(&class) {
            return (None, false);
        }
        seen.push(class);
        // Read-only scan: a direct ctor hit wins; otherwise collect the `ite`
        // triples in node order. Copy the ids out so the `&egraph` borrow ends
        // before the recursive `&mut egraph` calls below.
        let mut field = None;
        let mut ites: Vec<[Id; 3]> = Vec::new();
        for node in &egraph[class].nodes {
            match node {
                Symbolic::FuncApp(c, _, args) if *c == self.ctor && self.index < args.len() => {
                    field = Some(args[self.index]);
                    break;
                }
                Symbolic::Ite([c, t, e]) => ites.push([*c, *t, *e]),
                _ => {}
            }
        }
        let mut result = None;
        let mut acyclic = true;
        if let Some(f) = field {
            result = Some(f);
        } else {
            for [c, t, e] in ites {
                let (tr, ta) = self.project(egraph, t, memo, seen);
                acyclic &= ta;
                let Some(tid) = tr else { continue };
                let (er, ea) = self.project(egraph, e, memo, seen);
                acyclic &= ea;
                let Some(eid) = er else { continue };
                result = Some(egraph.add(Symbolic::Ite([c, tid, eid])));
                break;
            }
        }
        seen.pop();
        if acyclic {
            memo.insert(class, result);
        }
        (result, acyclic)
    }
}

impl Applier<Symbolic, ConstFold> for ProjApplier {
    fn apply_one(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<Symbolic>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let xc = egraph.find(subst[tag_x()]);
        let (Some(field), _) = self.project(egraph, xc, &mut HashMap::new(), &mut Vec::new()) else {
            return vec![];
        };
        if egraph.union(eclass, field) {
            vec![egraph.find(eclass)]
        } else {
            vec![]
        }
    }

    fn vars(&self) -> Vec<Var> {
        vec![tag_x()]
    }
}

// ---- Prepared pure bodies (axioms, quantifiers, function definitions) ------

/// A pure step of a prepared body. Mirrors the `PureInst` subset legal in an
/// axiom, with every callee resolved to its verifier `FuncId` up front (the
/// applier has no registry access) and its type arguments ground (only ADTs are
/// generic, and their instantiations are fixed at translation).
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) enum AxiomPure {
    Binary(BinOp, Val, Val),
    Ternary(Val, Val, Val),
    RealCast(Val),
    App {
        func: FuncId,
        type_args: Vec<Type>,
        args: Vec<Val>,
    },
    /// A fresh `wildcard` permission share (a resource footprint slot lowered
    /// from a function precondition). Each graft mints a new positive symbolic.
    Wildcard,
}

/// One instruction of a prepared body: a value-producing pure step, an
/// assumption (stitched from a callee's `#ensures`) merged with `true`, or a
/// nested `forall` — materialized as a [`Symbolic::Forall`] node whose capture
/// children are resolved through the *enclosing* instance's temps, so an outer
/// instantiation bakes its σ into the inner quantifier and the generic rule picks
/// the new node up on the next iteration.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) enum AxiomInst {
    Val(AxiomPure),
    Assume(Val),
    Forall { recipe: RecipeId, caps: Vec<Val> },
}

/// Searcher: any e-class containing an application of the trigger function
/// (type-blind — every ground instantiation lives in one `classes_by_op`
/// bucket, as in [`UnaryAppSearcher`]). σ extraction happens in the applier,
/// which re-reads the matched e-class's nodes (an egg `Subst` cannot carry
/// types).
struct AxiomTriggerSearcher {
    func: FuncId,
}

impl Searcher<Symbolic, ConstFold> for AxiomTriggerSearcher {
    fn search_with_limit(
        &self,
        egraph: &EGraph<Symbolic, ConstFold>,
        limit: usize,
    ) -> Vec<SearchMatches<'_, Symbolic>> {
        let Some(ids) = egraph.classes_for_op(&Discriminant::FuncApp(self.func)) else {
            return vec![];
        };
        let mut ms = Vec::new();
        let mut limit = limit;
        for eclass in ids {
            if limit == 0 {
                break;
            }
            if let Some(m) = self.search_eclass_with_limit(egraph, eclass, limit) {
                limit -= m.substs.len();
                ms.push(m);
            }
        }
        ms
    }

    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<Symbolic, ConstFold>,
        eclass: Id,
        _limit: usize,
    ) -> Option<SearchMatches<'_, Symbolic>> {
        let hit = egraph[eclass]
            .nodes
            .iter()
            .any(|n| matches!(n, Symbolic::FuncApp(f, _, _) if *f == self.func));
        hit.then(|| SearchMatches {
            eclass,
            // One empty subst: the applier extracts σ from the e-class itself.
            substs: vec![Subst::default()],
            ast: None,
        })
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// Add a prepared body (of an axiom, a quantifier, or a function definition) to
/// the e-graph, seeding the value slots with `vals_seed` (the captures ++
/// bound-variable σ for a quantifier, the arguments for a function definition;
/// empty for a closed axiom). Runs the body's `Assume`s (merging each with
/// `true`) and returns the changed e-classes together with the body's `res`
/// e-class id. The caller decides how to discharge `res` (an axiom merges it
/// with `true`; a quantifier guards it; a function unfold unions it with the
/// call e-class).
pub(crate) fn build_instance(
    egraph: &mut EGraph<Symbolic, ConstFold>,
    insts: &[AxiomInst],
    res: &Val,
    vals_seed: &[Id],
    changed: &mut Vec<Id>,
) -> Id {
    let vals = build_instance_vals(egraph, insts, vals_seed, changed);
    resolve_val(egraph, &vals, res)
}

/// [`build_instance`], but every `AxiomPure::Wildcard` step is replaced by the
/// fixed id `wildcard_repl` instead of a fresh positive wildcard. Used to build a
/// footprint slot's **presence** term (`wildcard → 1`, so `ite(guard, 1, 0)`
/// whose `0 < …` folds to `guard`) without ever minting a `Symbolic::Wildcard` —
/// keeping the un-collapsible wildcard `ite` out of the persistent graph.
pub(crate) fn build_instance_subst(
    egraph: &mut EGraph<Symbolic, ConstFold>,
    insts: &[AxiomInst],
    res: &Val,
    vals_seed: &[Id],
    changed: &mut Vec<Id>,
    wildcard_repl: Id,
) -> Id {
    let vals = build_instance_vals_impl(egraph, insts, vals_seed, changed, Some(wildcard_repl));
    resolve_val(egraph, &vals, res)
}

/// Resolve a recipe-space `Val` against a built instance's temp slots.
fn resolve_val(egraph: &mut EGraph<Symbolic, ConstFold>, vals: &[Id], v: &Val) -> Id {
    match v {
        Val::Temp(n) => vals[*n],
        Val::Literal(lit) => egraph.add(Symbolic::Lit(lit.clone())),
    }
}

/// [`build_instance`], but returning the **full** temp-slot map (seed ++ one
/// `Id` per step) so the caller can resolve several recipe values against one
/// built instance (a function definition's `res` plus its exported facts).
pub(crate) fn build_instance_vals(
    egraph: &mut EGraph<Symbolic, ConstFold>,
    insts: &[AxiomInst],
    vals_seed: &[Id],
    changed: &mut Vec<Id>,
) -> Vec<Id> {
    build_instance_vals_impl(egraph, insts, vals_seed, changed, None)
}

/// [`build_instance_vals`] with an optional wildcard substitution (see
/// [`build_instance_subst`]). `wildcard_repl = None` mints fresh wildcards.
fn build_instance_vals_impl(
    egraph: &mut EGraph<Symbolic, ConstFold>,
    insts: &[AxiomInst],
    vals_seed: &[Id],
    changed: &mut Vec<Id>,
    wildcard_repl: Option<Id>,
) -> Vec<Id> {
    let mut vals: Vec<Id> = vals_seed.to_vec();
    fn get(egraph: &mut EGraph<Symbolic, ConstFold>, vals: &[Id], v: &Val) -> Id {
        resolve_val(egraph, vals, v)
    }
    let true_of =
        |egraph: &mut EGraph<Symbolic, ConstFold>| egraph.add(Symbolic::Lit(Literal::Bool(true)));
    for inst in insts {
        match inst {
            AxiomInst::Val(p) => {
                let id = match p {
                    AxiomPure::Binary(op, l, r) => {
                        let l = get(egraph, &vals, l);
                        let r = get(egraph, &vals, r);
                        egraph.add(Symbolic::Binary(*op, [l, r]))
                    }
                    AxiomPure::Ternary(c, t, e) => {
                        let c = get(egraph, &vals, c);
                        let t = get(egraph, &vals, t);
                        let e = get(egraph, &vals, e);
                        egraph.add(Symbolic::Ite([c, t, e]))
                    }
                    AxiomPure::RealCast(v) => {
                        let v = get(egraph, &vals, v);
                        egraph.add(Symbolic::RealCast(v))
                    }
                    AxiomPure::App {
                        func,
                        type_args,
                        args,
                    } => {
                        let tys: Box<[Type]> = type_args.iter().cloned().collect();
                        let args: Box<[Id]> = args.iter().map(|v| get(egraph, &vals, v)).collect();
                        egraph.add(Symbolic::FuncApp(*func, tys, args))
                    }
                    AxiomPure::Wildcard => match wildcard_repl {
                        // Presence build: use the fixed replacement (a positive
                        // constant), no fresh wildcard.
                        Some(repl) => repl,
                        // Mint a fresh positive wildcard: `w` with `0 < w` assumed.
                        None => {
                            let w = egraph
                                .add(Symbolic::Wildcard(crate::verify::lang::fresh_wildcard_id()));
                            let zero = egraph
                                .add(Symbolic::Lit(Literal::Real(num::BigInt::from(0).into())));
                            let pos = egraph.add(Symbolic::Binary(BinOp::LtR, [zero, w]));
                            let t = true_of(egraph);
                            if egraph.union(pos, t) {
                                changed.push(egraph.find(pos));
                            }
                            w
                        }
                    },
                };
                vals.push(id);
            }
            AxiomInst::Assume(v) => {
                let id = get(egraph, &vals, v);
                let t = true_of(egraph);
                if egraph.union(id, t) {
                    changed.push(egraph.find(id));
                }
            }
            AxiomInst::Forall { recipe, caps } => {
                let caps: Box<[Id]> = caps.iter().map(|v| get(egraph, &vals, v)).collect();
                let id = egraph.add(Symbolic::Forall(*recipe, caps));
                vals.push(id);
            }
        }
    }
    vals
}

// ---- Pure `forall` quantifiers (value-σ triggered) -------------------------

/// One trigger pattern term, with every head resolved to its verifier `FuncId`
/// (the applier has no registry access). The `vmir::TrigTerm` grammar, flattened
/// to what the e-graph speaks: an `App` matches a `FuncApp` node with the same
/// function, type payload and arity, whose argument e-classes match `args`
/// recursively.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) enum PreparedTerm {
    Bound(usize),
    Capture(usize),
    Lit(Literal),
    App {
        func: FuncId,
        type_args: Box<[Type]>,
        args: Vec<PreparedTerm>,
    },
}

impl PreparedTerm {
    /// The function a term is rooted at — the searcher's anchor. Only an `App`
    /// can be a top-level trigger term (typecheck-enforced).
    fn root_func(&self) -> Option<FuncId> {
        match self {
            PreparedTerm::App { func, .. } => Some(*func),
            _ => None,
        }
    }
}

/// A partial bound-variable substitution, one slot per binder.
type Sigma = Vec<Option<Id>>;

/// Match `term` against e-class `class` under the forall node's capture children,
/// extending `sigma`. Returns every consistent extension (an e-class may hold
/// several nodes matching the pattern's head, each binding σ differently), or an
/// empty vector when the term cannot match.
fn match_term(
    egraph: &EGraph<Symbolic, ConstFold>,
    term: &PreparedTerm,
    class: Id,
    caps: &[Id],
    sigma: &Sigma,
) -> Vec<Sigma> {
    let class = egraph.find(class);
    match term {
        PreparedTerm::Bound(i) => match sigma[*i] {
            // A repeated binder must land on the same e-class.
            Some(prev) if egraph.find(prev) != class => vec![],
            Some(_) => vec![sigma.clone()],
            None => {
                let mut next = sigma.clone();
                next[*i] = Some(class);
                vec![next]
            }
        },
        PreparedTerm::Capture(c) => {
            if egraph.find(caps[*c]) == class {
                vec![sigma.clone()]
            } else {
                vec![]
            }
        }
        PreparedTerm::Lit(lit) => {
            if egraph[class]
                .nodes
                .iter()
                .any(|n| matches!(n, Symbolic::Lit(l) if l == lit))
            {
                vec![sigma.clone()]
            } else {
                vec![]
            }
        }
        PreparedTerm::App {
            func,
            type_args,
            args,
        } => {
            let mut out = Vec::new();
            for node in &egraph[class].nodes {
                let Symbolic::FuncApp(f, tys, children) = node else {
                    continue;
                };
                if f != func || tys != type_args || children.len() != args.len() {
                    continue;
                }
                // Thread σ left to right across the arguments, branching on every
                // consistent way each of them matches.
                let mut partials = vec![sigma.clone()];
                for (arg, &child) in args.iter().zip(children.iter()) {
                    partials = partials
                        .iter()
                        .flat_map(|s| match_term(egraph, arg, child, caps, s))
                        .collect();
                    if partials.is_empty() {
                        break;
                    }
                }
                out.extend(partials);
            }
            out
        }
    }
}

/// Every σ that matches `term` somewhere in the e-graph, extending `sigma`. Scans
/// the classes holding an application of the term's root function.
fn match_term_anywhere(
    egraph: &EGraph<Symbolic, ConstFold>,
    term: &PreparedTerm,
    caps: &[Id],
    sigma: &Sigma,
) -> Vec<Sigma> {
    let Some(root) = term.root_func() else {
        return vec![];
    };
    let Some(classes) = egraph.classes_for_op(&Discriminant::FuncApp(root)) else {
        return vec![];
    };
    classes
        .flat_map(|class| match_term(egraph, term, class, caps, sigma))
        .collect()
}

/// Searcher for the **single** quantifier-instantiation rule: every e-class
/// holding a `Forall` node, found through `classes_for_op` (one bucket per
/// recipe — indexed, no whole-graph scan). Quantifiers are *data*, not rules, so
/// a `forall` materialized mid-run is picked up on the next iteration; egg
/// forbids injecting rules mid-`Runner`.
struct ForallSearcher {
    table: Arc<RecipeTable>,
}

impl Searcher<Symbolic, ConstFold> for ForallSearcher {
    fn search_with_limit(
        &self,
        egraph: &EGraph<Symbolic, ConstFold>,
        limit: usize,
    ) -> Vec<SearchMatches<'_, Symbolic>> {
        let mut ms = Vec::new();
        let mut limit = limit;
        for rid in self.table.ids() {
            let Some(classes) = egraph.classes_for_op(&Discriminant::Forall(rid)) else {
                continue;
            };
            for eclass in classes {
                if limit == 0 {
                    return ms;
                }
                limit -= 1;
                ms.push(SearchMatches {
                    eclass,
                    // One empty subst: the applier reads the node itself (recipe
                    // + captures), which an egg `Subst` cannot carry.
                    substs: vec![Subst::default()],
                    ast: None,
                });
            }
        }
        ms
    }

    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<Symbolic, ConstFold>,
        eclass: Id,
        _limit: usize,
    ) -> Option<SearchMatches<'_, Symbolic>> {
        egraph[eclass]
            .nodes
            .iter()
            .any(|n| matches!(n, Symbolic::Forall(..)))
            .then(|| SearchMatches {
                eclass,
                substs: vec![Subst::default()],
                ast: None,
            })
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// Applier: for the matched forall e-class, take each `Forall(recipe, caps)` node
/// in it and pair it with every σ under which one of its recipe's trigger groups
/// matches the graph. Instantiate the body at `caps ++ σ` and add the **guarded**
/// clause `Ite(forall, res[caps, σ], true) == true`: the instance is released only
/// once that forall e-class merges `true` (existing `ite-true` rule), so
/// instantiating is sound regardless of the quantifier's truth.
///
/// Memoized per `(recipe, caps ++ σ)` (canonicalized at insert) — a saturation-cost
/// guard only, since instances are idempotent.
struct ForallApplier {
    table: Arc<RecipeTable>,
    memo: Arc<Memo<(RecipeId, Vec<Id>)>>,
}

impl Applier<Symbolic, ConstFold> for ForallApplier {
    fn apply_one(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        eclass: Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<Symbolic>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        // Distinct capture tuples in one e-class are distinct quantifiers (each
        // yields its own instances); the guard is this e-class either way.
        let quants: Vec<(RecipeId, Box<[Id]>)> = egraph[eclass]
            .nodes
            .iter()
            .filter_map(|n| match n {
                Symbolic::Forall(rid, caps) => Some((*rid, caps.clone())),
                _ => None,
            })
            .collect();

        // Collect the instances first: `build_instance` needs `&mut egraph`.
        let mut instances: Vec<(RecipeId, Vec<Id>)> = Vec::new();
        for (rid, caps) in &quants {
            let recipe = self.table.get(*rid);
            let caps: Vec<Id> = caps.iter().map(|&c| egraph.find(c)).collect();
            for group in &recipe.groups {
                let Some((anchor, rest)) = group.split_first() else {
                    continue;
                };
                let empty: Sigma = vec![None; recipe.n_bound];
                let mut sigmas = match_term_anywhere(egraph, anchor, &caps, &empty);
                for term in rest {
                    sigmas = sigmas
                        .iter()
                        .flat_map(|s| match_term_anywhere(egraph, term, &caps, s))
                        .collect();
                    if sigmas.is_empty() {
                        break;
                    }
                }
                for sigma in sigmas {
                    // A group covers every binder (typecheck-enforced), so a
                    // complete match leaves no slot open.
                    let Some(sigma): Option<Vec<Id>> = sigma.into_iter().collect() else {
                        continue;
                    };
                    // The seed is the body's leading temps: captures then binders.
                    let mut vals = caps.clone();
                    vals.extend(sigma);
                    if self.memo.insert((*rid, vals.clone())) {
                        instances.push((*rid, vals));
                    }
                }
            }
        }

        let mut changed = Vec::new();
        for (rid, vals) in instances {
            let recipe = self.table.get(rid);
            debug_assert_eq!(
                vals.len(),
                recipe.n_caps + recipe.n_bound,
                "instance seed is captures ++ sigma"
            );
            let res = build_instance(egraph, &recipe.insts, &recipe.res, &vals, &mut changed);
            let true_ = egraph.add(Symbolic::Lit(Literal::Bool(true)));
            let guard = egraph.add(Symbolic::Ite([eclass, res, true_]));
            if egraph.union(guard, true_) {
                changed.push(egraph.find(guard));
            }
        }
        changed
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// The one rule that instantiates **every** `forall` in the program. Quantifiers
/// are e-nodes, so this replaces the old per-quantifier, per-trigger-group rule
/// minting entirely.
pub(crate) fn forall_rule(table: Arc<RecipeTable>) -> Rule {
    let searcher = ForallSearcher {
        table: Arc::clone(&table),
    };
    let applier = ForallApplier {
        table,
        memo: Arc::new(Memo::new()),
    };
    timed(Rewrite::new("forall-instantiate", searcher, applier).expect("forall rule"))
}

// ---- Function-call unfolding (lazy, rewrite-rule triggered) ---------------

/// A canonicalized call key: the ground `(type_args, value_args)` an occurrence
/// of the function was applied to. Memoized so the recipe rebuilds once per call.
type CallKey = (Box<[Type]>, Vec<Id>);

/// Applier: for each ground `FuncApp(self.func, tys, args)` node in the matched
/// e-class, rebuild the function's **definition recipe** with `build_instance`
/// (params → args, `Generic(i)` → `tys`) and union the result with the matched
/// e-class, installing `f(args) == body` lazily as occurrences are seen during
/// saturation. **Add-only** (`build_instance` imports no e-classes), so merges
/// derived while verifying the body itself never ride along. Works uniformly for
/// heap-free and heap-dependent `f`: the recipe already resolved every
/// `Deref`/`Unfold`/`Snap` into pure terms over the params + snapshot.
struct FunctionUnfoldApplier {
    func: FuncId,
    def: Arc<FunctionDefinition>,
    /// `false`: the full rule (keyed on `f`) — definitional union, limited
    /// framing, and every exported fact. `true`: the limited-post rule (keyed
    /// on `f'`) — replays **only** post facts, no unions: unfolding a recursive
    /// body yields `f'(smaller)`, and this is what delivers the postcondition
    /// there (Silicon's `post` axiom triggering on the limited symbol).
    limited_post: bool,
    /// Guards the (expensive) body build + fact replay: done at most once per call.
    memo: Memo<CallKey>,
    /// Guards the definitional union separately from the build: a call first built
    /// facts-only (no token yet) and later reached by a propagation-minted token
    /// must still union `f==body`, which `memo` alone would suppress.
    union_memo: Memo<CallKey>,
    /// The function's uniform pre-token `f%pre` (`FuncRegistry::fn_pre_token`),
    /// used as a `forall`-style **presence** trigger: the definitional
    /// `f(fargs)==body` union+build fires only when a `FuncApp(f%pre, fargs)` node
    /// is present for the *same* `fargs`, i.e. this occurrence came from a genuine
    /// value-position call. Mirrors Silicon's `f%pre ⟹ f==body`. `None` on the
    /// facts-only rule, where there is no definitional union to gate.
    pre_token: Option<FuncId>,
}

/// Replay a definition's exported facts against one built instance: for each
/// fact, merge `guards ⟹ cond` (an `Ite` chain, innermost-first — the shape
/// `VerifyContext::implication` builds) with `true`. Guarded, so a fact never
/// fires outside its pre-token + path condition.
fn replay_facts(
    egraph: &mut EGraph<Symbolic, ConstFold>,
    def: &FunctionDefinition,
    only_post: bool,
    vals: &[Id],
    changed: &mut Vec<Id>,
) {
    let true_ = egraph.add(Symbolic::Lit(Literal::Bool(true)));
    for fact in &def.facts {
        if only_post && !fact.post {
            continue;
        }
        let mut imp = resolve_val(egraph, vals, &fact.cond);
        for (g, pol) in fact.guards.iter().rev() {
            let g = resolve_val(egraph, vals, g);
            imp = match pol {
                Polarity::Positive => egraph.add(Symbolic::Ite([g, imp, true_])),
                Polarity::Negative => egraph.add(Symbolic::Ite([g, true_, imp])),
            };
        }
        if egraph.union(imp, true_) {
            changed.push(egraph.find(imp));
        }
    }
}

impl Applier<Symbolic, ConstFold> for FunctionUnfoldApplier {
    fn apply_one(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        eclass: Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<Symbolic>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        // Candidate calls in this e-class (deduped locally; the persistent `memo`
        // is only consulted once we commit to building — see below).
        let mut calls: Vec<(Box<[Type]>, Vec<Id>)> = Vec::new();
        for node in &egraph[eclass].nodes {
            let Symbolic::FuncApp(f, tys, args) = node else {
                continue;
            };
            if *f != self.func {
                continue;
            }
            let args: Vec<Id> = args.iter().map(|&a| egraph.find(a)).collect();
            let key = (tys.clone(), args);
            if !calls.contains(&key) {
                calls.push(key);
            }
        }
        let mut changed = Vec::new();
        for (tys, args) in calls {
            debug_assert_eq!(args.len(), self.def.n_params, "function unfold arity");
            // Presence trigger (see `pre_token`). Presence, NOT truth: the token is
            // released `assume_guarded` under the call-site PC, so its class is an
            // `ite(pc, tok, ..)` shape, never unconditionally `true`. Type args are
            // not in the `FuncApp` congruence key, so `[]` matches any
            // instantiation. `pre_token = None` ⇒ ungated (a contract
            // `#requires`/`#ensures` boolean, whose role is to inline its formula).
            let has_token = self.pre_token.is_none_or(|tok| {
                egraph
                    .lookup(Symbolic::FuncApp(tok, Box::new([]), args.clone().into()))
                    .is_some()
            });
            // The body instance is needed for the definitional union (token
            // present, non-limited) and for fact replay (facts reference body
            // temps). A call with neither needs no build — and must NOT be memoized,
            // so it can fire later once propagation mints its token mid-saturation.
            let do_union = !self.limited_post && has_token;
            let need_build = do_union || !self.def.facts.is_empty();
            if !need_build {
                continue;
            }
            let key = (tys.clone(), args.clone());
            let first_build = self.memo.insert(key.clone());
            // `do_union` is short-circuited first so the union memo is only ever
            // touched when the token is present: a fresh union, or a call built
            // facts-only earlier and now reached by a propagation-minted token.
            let do_union_now = do_union && self.union_memo.insert(key);
            // Nothing new to do: already built and no (new) union due.
            if !first_build && !do_union_now {
                continue;
            }
            let vals = build_instance_vals(egraph, &self.def.steps, &args, &mut changed);
            // Definitional union `f(args) == body` — unconditional once triggered:
            // the purified body is a total function of the args (Deref became
            // `unwrap∘proj`, div is total in the e-graph), so the equation holds
            // even at pre-violating args. Absent for an abstract function.
            if do_union_now {
                if let Some(res) = &self.def.res {
                    let result = resolve_val(egraph, &vals, res);
                    if egraph.union(eclass, result) {
                        changed.push(egraph.find(eclass));
                    }
                }
            }
            // Recursive function: frame the full occurrence to its limited twin
            // `f(args) == f'(args)`. `f'` has no unfold rule, so a limited call
            // produced by unfolding `f`'s body never re-unfolds (bounding
            // saturation); the frame lets a materialized `f(args)` value flow to
            // any `f'(args)` a sibling unfold produced.
            //
            // **Ungated**, matching Silicon's `limitedAxiom`. It must NOT sit
            // behind the `f%pre` presence token: the token is minted only at a
            // value-position call, so gating strands a recursive function's post
            // fact (stated on `f'`) in limited space whenever the occurrence
            // arrived via a callee's `ensures` rather than a direct call.
            //
            // Cannot reintroduce unbounded unfolding: this mints `f'` *from* an
            // existing `f` node, never the reverse, and the unfold rule filters
            // on `FuncApp(f)`.
            if !self.limited_post {
                if let Some(lim) = self.def.limited {
                    let twin = egraph.add(Symbolic::FuncApp(lim, tys.clone(), args.into()));
                    if egraph.union(eclass, twin) {
                        changed.push(egraph.find(eclass));
                    }
                }
            }
            // Replay facts only on the first build (idempotent; guarded internally).
            if first_build {
                replay_facts(egraph, &self.def, self.limited_post, &vals, &mut changed);
            }
        }
        changed
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// Mint the lazy-unfolding rule for one verified function's definition recipe.
/// Reuses [`AxiomTriggerSearcher`] as-is — it only checks `FuncApp(f, ..)`
/// presence, independent of arity/type-args, exactly what's needed here too.
pub(crate) fn function_rule(
    name: &str,
    func: FuncId,
    def: Arc<FunctionDefinition>,
    pre_token: Option<FuncId>,
) -> Rule {
    let searcher = AxiomTriggerSearcher { func };
    let applier = FunctionUnfoldApplier {
        func,
        def,
        limited_post: false,
        memo: Memo::new(),
        union_memo: Memo::new(),
        pre_token,
    };
    timed(Rewrite::new(format!("fn-{name}"), searcher, applier).expect("function rule"))
}

/// Mint a facts-only rule keyed on `func`: replays only the definition's post
/// facts, no definitional union. Two users:
/// - the limited-twin post rule of a recursive function ([`function_post_rule`]);
/// - the spec-derived post rule installed for each SCC member **during** a
///   recursive batch's own verification, which is what makes induction over a
///   recursive call work (Silicon's phase-1 `post` axiom).
pub(crate) fn facts_rule(name: &str, func: FuncId, def: Arc<FunctionDefinition>) -> Rule {
    let searcher = AxiomTriggerSearcher { func };
    let applier = FunctionUnfoldApplier {
        func,
        def,
        limited_post: true,
        memo: Memo::new(),
        union_memo: Memo::new(),
        // Facts-only rule: no definitional union, so no token gate.
        pre_token: None,
    };
    timed(Rewrite::new(format!("fn-post-{name}"), searcher, applier).expect("function post rule"))
}

/// Mint the limited-twin post rule for a **recursive** function: keyed on
/// `f'(args)` occurrences (which unfolding a recursive body produces), replays
/// only the definition's post facts (no definitional union — that's the point
/// of the limited symbol). Registered alongside [`function_rule`] when
/// `def.limited` is set and a post fact exists.
pub(crate) fn function_post_rule(name: &str, def: Arc<FunctionDefinition>) -> Rule {
    let func = def.limited.expect("post rule requires a limited twin");
    facts_rule(name, func, def)
}

#[cfg(test)]
mod bench {
    //! Micro-benchmark: the production [`UnaryAppSearcher`] (seeds from egg's
    //! `classes_by_op` op-index via its `search_with_limit` override) vs an
    //! otherwise-identical searcher that uses egg's default whole-e-graph scan.
    //!
    //! Run with: `cargo test --lib --release rewrite::bench -- --ignored --nocapture`.
    use super::*;
    use crate::verify::analysis::ConstFold;
    use egg::Runner;
    use std::time::{Duration, Instant};

    /// Same per-e-class match logic as [`UnaryAppSearcher`] but **without** the
    /// `search_with_limit` override — so it inherits egg's default, which scans
    /// every e-class in the graph. This is the "before" baseline.
    struct ScanSearcher {
        func: FuncId,
    }

    impl Searcher<Symbolic, ConstFold> for ScanSearcher {
        fn search_eclass_with_limit(
            &self,
            egraph: &EGraph<Symbolic, ConstFold>,
            eclass: Id,
            limit: usize,
        ) -> Option<SearchMatches<'_, Symbolic>> {
            let mut substs = Vec::new();
            for node in &egraph[eclass].nodes {
                if let Symbolic::FuncApp(f, _, args) = node
                    && *f == self.func
                    && args.len() == 1
                {
                    let mut subst = Subst::default();
                    subst.insert(tag_x(), args[0]);
                    substs.push(subst);
                    if substs.len() >= limit {
                        break;
                    }
                }
            }
            if substs.is_empty() {
                None
            } else {
                Some(SearchMatches {
                    eclass,
                    substs,
                    ast: None,
                })
            }
        }

        fn vars(&self) -> Vec<Var> {
            vec![tag_x()]
        }
    }

    /// Build an e-graph with `n_concepts` distinct ADT-like concepts — each a
    /// `proj(cons(x))` tower with its own `(cons, proj)` `FuncId`s — plus
    /// `n_filler` unrelated singleton e-classes that match no proj rule (the work
    /// the whole-graph scan wastes time on). Returns the graph and the concepts.
    fn build(
        n_concepts: usize,
        n_filler: usize,
    ) -> (EGraph<Symbolic, ConstFold>, Vec<(FuncId, FuncId)>) {
        let mut g = EGraph::<Symbolic, ConstFold>::default();
        let mut concepts = Vec::with_capacity(n_concepts);
        for i in 0..n_concepts {
            let cons_id = FuncId(1000 + 2 * i);
            let proj_id = FuncId(1000 + 2 * i + 1);
            let x = g.add(Symbolic::Fresh(i as u32));
            let cons = g.add(Symbolic::FuncApp(cons_id, Box::new([]), Box::new([x])));
            g.add(Symbolic::FuncApp(proj_id, Box::new([]), Box::new([cons])));
            concepts.push((cons_id, proj_id));
        }
        for j in 0..n_filler {
            g.add(Symbolic::Fresh(1_000_000 + j as u32));
        }
        g.rebuild();
        (g, concepts)
    }

    /// Best wall-clock of 5 saturation runs over a fresh clone of `g`.
    fn best_of_5(g: &EGraph<Symbolic, ConstFold>, rules: &[Rule]) -> Duration {
        let mut best = Duration::MAX;
        for _ in 0..5 {
            let eg = g.clone();
            let start = Instant::now();
            let runner = Runner::default()
                .with_node_limit(10_000_000)
                .with_iter_limit(100)
                .with_time_limit(Duration::from_secs(120))
                .with_egraph(eg)
                .run(rules);
            best = best.min(start.elapsed());
            std::hint::black_box(runner.egraph.total_size());
        }
        best
    }

    #[test]
    #[ignore = "perf benchmark; run explicitly with --ignored --nocapture"]
    fn indexed_searcher_beats_whole_graph_scan() {
        let n_concepts = 500;
        let n_filler = 20_000;
        let (g, concepts) = build(n_concepts, n_filler);

        let indexed: Vec<Rule> = concepts.iter().map(|(c, p)| proj_rule(*p, *c, 0)).collect();
        let naive: Vec<Rule> = concepts
            .iter()
            .map(|(c, p)| {
                Rewrite::new(
                    format!("scan-{}", p.0),
                    ScanSearcher { func: *p },
                    ProjApplier { ctor: *c, index: 0 },
                )
                .expect("valid rule")
            })
            .collect();

        let t_naive = best_of_5(&g, &naive);
        let t_indexed = best_of_5(&g, &indexed);

        eprintln!(
            "concepts={n_concepts} filler_eclasses={n_filler} rules={}",
            concepts.len()
        );
        eprintln!("whole-graph scan : {t_naive:?}");
        eprintln!("classes_by_op    : {t_indexed:?}");
        eprintln!(
            "speedup          : {:.1}x",
            t_naive.as_secs_f64() / t_indexed.as_secs_f64().max(f64::MIN_POSITIVE)
        );
        assert!(
            t_indexed < t_naive,
            "indexed seeding should beat the whole-graph scan"
        );
    }
}
