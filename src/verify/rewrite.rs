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

/// The current memo generation — one per [`egg::Runner`] run.
///
/// An applier's memo ("already instantiated this call/σ") is a pure cost guard:
/// re-instantiating is idempotent (adds hash-cons, unions no-op). But it is
/// keyed on the e-class ids of *one* e-graph, and a `Rewrite`'s applier lives
/// behind an `Arc` — cloning the rule list per run shares it. `prove_under_pc`'s
/// tier 3 saturates a **clone** and throws the result away, so a memo carried
/// across runs would record instantiations whose unions no longer exist,
/// starving every later run of them (a completeness bug: goals that hold become
/// unprovable, depending on what an earlier probe happened to touch). Bumping
/// the generation before each run scopes the memo to that run.
static MEMO_GEN: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Start a new memo generation. Call before every [`egg::Runner`] run.
pub(crate) fn new_memo_generation() {
    MEMO_GEN.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}

/// A run-scoped applier memo (see [`MEMO_GEN`]).
pub(crate) struct Memo<K>(Mutex<(u64, HashSet<K>)>);

impl<K: Eq + std::hash::Hash> Memo<K> {
    fn new() -> Self {
        Self(Mutex::new((u64::MAX, HashSet::new())))
    }

    /// `true` when `key` has not been seen *in the current generation*.
    fn insert(&self, key: K) -> bool {
        let generation = MEMO_GEN.load(std::sync::atomic::Ordering::Relaxed);
        let mut memo = self.0.lock().unwrap();
        if memo.0 != generation {
            memo.0 = generation;
            memo.1.clear();
        }
        memo.1.insert(key)
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
    static_rules().into_iter().map(timed).collect()
}

/// The terminating structural reductions used to **normalize** the e-graph after
/// heap-producing ops (`fold`/`unfold`): the terminating `ite`/optional
/// simplifications (which peel the `(perm>0) ? Some(v) : None` wrapper down to
/// `v` whenever the permission is statically positive). The registry's ADT
/// reductions (which collapse `cons(proj(cons(..)))` snapshot towers) are
/// appended by `VerifyContext::new`. Kept separate from [`rules`] so that future
/// *non-terminating* rules are run only during full saturation, never here.
pub fn reduce_rules() -> Vec<Rule> {
    terminating_ite_rules().into_iter().map(timed).collect()
}

/// Build the projection reduction `accessor(ctor(a0..an)) ⇒ a_index` for a
/// single (possibly verifier-synthesised, e.g. monomorphic) member id. Lets the
/// verifier register reductions for member ids minted after `VerifyContext`
/// construction (monomorphic Option instances).
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
/// Congruence alone only runs *forward* (equal args ⟹ equal applications), and
/// [`proj_rule`] recovers the backward direction only where a `projᵢ`
/// application happens to exist in the graph. Two constructor terms can land in
/// one class with no projection over them — e.g. a predicate snapshot function's
/// body (`cons(snap(f0), snap(f1))`) meeting the value it was assigned
/// (`cons(x, y)` from some other function's body) — and then the component
/// equalities are only reachable through this rule.
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
        // x + 0 => x  (Int)
        rw!("add-zero-int-r"; "(+ ?x 0)" => "?x"),
        rw!("add-zero-int-l"; "(+ 0 ?x)" => "?x"),
        // x + 0 => x  (Real zero literal `0/1`; `real(0)` const-folds to it)
        rw!("add-zero-real-r"; "(+ ?x 0/1)" => "?x"),
        rw!("add-zero-real-l"; "(+ 0/1 ?x)" => "?x"),
        // x * 1 => x  (Real one literal `1/1`; resource-delta perm scaling by a
        // full permission `write` folds away)
        rw!("mul-one-real-r"; "(* ?x 1/1)" => "?x"),
        rw!("mul-one-real-l"; "(* 1/1 ?x)" => "?x"),
        // x == x => true   (reflexivity; also fires when congruence has already
        // merged the two operands into one e-class, e.g. a return var copied from
        // a param: `ensures r == a` after `r := a`).
        rw!("eq-refl"; "(== ?x ?x)" => "true"),
        // (a == b) proven true  =>  a ≡ b   (congruence)
        rw!("eq-true-union"; "(== ?a ?b)" => {
            UnionEqArgs { a: var("?a"), b: var("?b") }
        }),
        // The boolean decompositions (and-true, or-false, not-true) live in the
        // fused `ite-reduce` pass — they are `Ite`-bucket shapes conditioned on
        // the class's proven boolean, exactly what its applier already inspects.
    ]);
    rules.extend(distributive_ite_rules());
    rules
}

/// Rules that push down the builtin operators into the ite branches.
fn distributive_ite_rules() -> Vec<Rule> {
    vec![
        // // EQ rules
        // rw!("eq-ite-l"; "(== (ite ?c ?x ?y) ?z)" => "(ite ?c (== ?x ?z) (== ?y ?z))"),
        // rw!("eq-ite-r"; "(== ?z (ite ?c ?x ?y))" => "(ite ?c (== ?z ?x) (== ?z ?y))"),
        // LT rules. The left form is load-bearing: CFG linearization encodes a
        // conditional inhale/exhale as a *scaled permission* `c ? p : 0`, so the
        // permission ≥ 0 obligation of such an instruction is a `<` applied to
        // an `ite`. Pushing the `<` inward lets `ConstFold` decide each branch,
        // after which `ite-same` collapses the result. Terminating: strictly
        // reduces the `ite` nesting above the `<`.
        rw!("lt-ite-l"; "(< (ite ?c ?x ?y) ?z)" => "(ite ?c (< ?x ?z) (< ?y ?z))"),
        // rw!("lt-ite-r"; "(< ?z (ite ?c ?x ?y))" => "(ite ?c (< ?z ?x) (< ?z ?y))"),
        // // MULT rules
        // rw!("mult-ite-l"; "(* (ite ?c ?x ?y) ?z)" => "(ite ?c (* ?x ?z) (* ?y ?z))"),
        // rw!("mult-ite-r"; "(* ?z (ite ?c ?x ?y))" => "(ite ?c (* ?z ?x) (* ?z ?y))"),
        // // PLUS rules
        // rw!("plus-ite-l"; "(+ (ite ?c ?x ?y) ?z)" => "(ite ?c (+ ?x ?z) (+ ?y ?z))"),
        // rw!("plus-ite-r"; "(+ ?z (ite ?c ?x ?y))" => "(ite ?c (+ ?z ?x) (+ ?z ?y))"),
        // // MINUS rules
        // rw!("minus-ite-l"; "(- (ite ?c ?x ?y) ?z)" => "(ite ?c (- ?x ?z) (- ?y ?z))"),
        // rw!("minus-ite-r"; "(- ?z (ite ?c ?x ?y))" => "(ite ?c (- ?z ?x) (- ?z ?y))"),
        // // REAL rules
        // rw!("real-ite"; "(real (ite ?c ?x ?y))" => "(ite ?c (real ?x) (real ?y))"),
    ]
}

/// Terminating `ite` simplifications. Shared by the saturation rule set and the
/// post-`fold`/`unfold` reduction set. Under an assumed branch literal (on the
/// instruction's path condition) `ite-true`/`ite-false` reduce a gated
/// permission `b ? p : 0` to `p` (resp. `0`), which is what discharges a
/// conditional `acc`'s permission ≥ 0 obligation and peels the optional snapshot
/// member's discriminant. When no such literal is available (a CFG-linearized
/// conditional inhale carries its guard in the permission, not the path
/// condition), the saturation-only `lt-ite` rule distributes the comparison
/// instead.
/// The terminating `ite` simplifications, fused into **one** rule that scans
/// the `Ite` op bucket once per iteration and node-checks every shape. The
/// twelve equivalent `rw!` patterns cost ~70% of all search time on real
/// programs: `implication()` encodes every guard as an `Ite` tower, so the
/// bucket holds thousands of classes, and the nested two-level patterns
/// (`ite-collapse-*`, `ite-nested-*`) pay a backtracking cross-product over it
/// per pattern per iteration. The fused pass is linear in the bucket (plus the
/// nodes of the two branch classes for the nested shapes) and union-only.
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
            // Nested same-condition ite in the true branch:
            //   c ? (c ? x : y) : e
            for inner in &egraph[t].nodes {
                let Symbolic::Ite([c2, x, y]) = inner else {
                    continue;
                };
                if egraph.find(*c2) != c {
                    continue;
                }
                // c ? (c ? x : y) : x => x
                if egraph.find(*x) == e {
                    unions.push((eclass, Target::Class(e)));
                }
                // c ? (c ? x : y) : y => c ? x : y
                if egraph.find(*y) == e {
                    unions.push((eclass, Target::Class(t)));
                }
            }
            // Nested same-condition ite in the false branch:
            //   c ? t : (c ? x : y)
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
                }
                // c ? x : (c ? x : y) => c ? x : y
                if egraph.find(*x) == t {
                    unions.push((eclass, Target::Class(e)));
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

/// Applier for the projection reduction: if the argument's e-class holds the
/// matching constructor `ctor`, union the `accessor(..)` e-class with that
/// constructor's `index`-th value argument. (Type args are not children, so the
/// value args start at 0.)
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

struct ProjApplier {
    ctor: FuncId,
    index: usize,
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
        let mut field = None;
        for node in &egraph[xc].nodes {
            if let Symbolic::FuncApp(c, _, args) = node
                && *c == self.ctor
                && self.index < args.len()
            {
                field = Some(args[self.index]);
                break;
            }
        }
        let Some(field) = field else { return vec![] };
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
}

/// One instruction of a prepared body: a value-producing pure step, an
/// assumption (stitched from a callee's `#ensures`) merged with `true`, or a
/// nested `forall` — materialized as a [`Symbolic::Forall`] node whose capture
/// children are resolved through the *enclosing* instance's temps. That last arm
/// is all closure-converted nesting needs: an outer instantiation builds the
/// inner quantifier with the outer σ baked into its children, and the generic
/// rule picks the new node up on the next iteration.
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
/// a `forall` materialized mid-run by an outer instantiation or a certificate
/// graft is picked up on the very next iteration — the thing per-quantifier
/// rules structurally cannot do (egg forbids rule injection mid-`Runner`).
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

/// Applier: for each ground `FuncApp(self.func, tys, args)` node in the matched
/// e-class, rebuild the function's **definition recipe** with `build_instance`
/// (params → args, `Generic(i)` → `tys`) and union the result with the matched
/// e-class — installing `f(args) == body` lazily, the moment an occurrence is
/// seen during saturation, instead of eagerly at translation-walk time. Unlike
/// the old certificate graft this is **add-only** (`build_instance` imports no
/// e-classes), so precondition-derived merges from the body's own verification
/// never ride along (Finding B). Works uniformly for heap-free and
/// heap-dependent `f`: the recipe already resolved every `Deref`/`Unfold`/`Snap`
/// into pure terms over the params + snapshot. Memoized per canonicalized
/// `(tys, args)` tuple (a saturation-cost guard; rebuilding is idempotent).
/// A canonicalized call key: the ground `(type_args, value_args)` an occurrence
/// of the function was applied to. Memoized so the recipe rebuilds once per call.
type CallKey = (Box<[Type]>, Vec<Id>);

struct FunctionUnfoldApplier {
    func: FuncId,
    def: Arc<FunctionDefinition>,
    /// `false`: the full rule (keyed on `f`) — definitional union, limited
    /// framing, and every exported fact. `true`: the limited-post rule (keyed
    /// on `f'`) — replays **only** post facts, no unions: unfolding a recursive
    /// body yields `f'(smaller)`, and this is what delivers the postcondition
    /// there (Silicon's `post` axiom triggering on the limited symbol).
    limited_post: bool,
    memo: Memo<CallKey>,
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
            if self.memo.insert(key.clone()) {
                calls.push(key);
            }
        }
        let mut changed = Vec::new();
        for (tys, args) in calls {
            debug_assert_eq!(args.len(), self.def.n_params, "function unfold arity");
            let vals = build_instance_vals(egraph, &self.def.steps, &args, &mut changed);
            // Definitional union `f(args) == body` — unconditional: the
            // purified body is a total function of the args (Deref became
            // `unwrap∘proj`, div is total in the e-graph), so the equation
            // holds even at pre-violating args. Sound only while nothing else
            // constrains `f` there — which Viper's ban on program functions in
            // domain axioms guarantees. Absent for an abstract function.
            if !self.limited_post {
                if let Some(res) = &self.def.res {
                    let result = resolve_val(egraph, &vals, res);
                    if egraph.union(eclass, result) {
                        changed.push(egraph.find(eclass));
                    }
                }
                // Recursive function: frame the full occurrence to its limited twin
                // `f(args) == f'(args)`. `f'` has no unfold rule, so a limited call
                // produced by unfolding `f`'s body never re-unfolds (bounding
                // saturation); the frame lets a materialized `f(args)` value flow to
                // any `f'(args)` a sibling unfold produced.
                if let Some(lim) = self.def.limited {
                    let twin = egraph.add(Symbolic::FuncApp(lim, tys.clone(), args.into()));
                    if egraph.union(eclass, twin) {
                        changed.push(egraph.find(eclass));
                    }
                }
            }
            replay_facts(egraph, &self.def, self.limited_post, &vals, &mut changed);
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
pub(crate) fn function_rule(name: &str, func: FuncId, def: Arc<FunctionDefinition>) -> Rule {
    let searcher = AxiomTriggerSearcher { func };
    let applier = FunctionUnfoldApplier {
        func,
        def,
        limited_post: false,
        memo: Memo::new(),
    };
    timed(Rewrite::new(format!("fn-{name}"), searcher, applier).expect("function rule"))
}

/// Mint a facts-only rule keyed on `func`: replays only the definition's post
/// facts, no definitional union. Two users:
/// - the limited-twin post rule of a recursive function ([`function_post_rule`]);
/// - the spec-derived post rule installed for each SCC member **during** a
///   recursive batch's own verification (Silicon's phase-1 `post` axiom is
///   available while checking the body — that is what makes induction over a
///   recursive call work).
pub(crate) fn facts_rule(name: &str, func: FuncId, def: Arc<FunctionDefinition>) -> Rule {
    let searcher = AxiomTriggerSearcher { func };
    let applier = FunctionUnfoldApplier {
        func,
        def,
        limited_post: true,
        memo: Memo::new(),
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
