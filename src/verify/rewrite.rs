//! Structural egg rewrite rules for the verifier.

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

use egg::{
    Applier, EGraph, Id, PatternAst, Rewrite, SearchMatches, Searcher, Subst, Symbol, Var,
    rewrite as rw,
};

use crate::verify::analysis::ConstFold;
use crate::verify::context::{FunctionCertificate, TransplantSink, Transplanted, transplant};
use crate::verify::lang::{Discriminant, FuncId, Symbolic};
use crate::vmir::{BinOp, Literal, TrigArg, Type, Val};

type Rule = Rewrite<Symbolic, ConstFold>;

fn var(name: &str) -> Var {
    name.parse().expect("valid pattern var")
}

/// The static structural rule set. Per-ADT cons/proj/tag reductions are minted
/// by the registry (`verify::mono`) and appended by `VerifyContext::new`.
pub fn rules() -> Vec<Rule> {
    static_rules()
}

/// The terminating structural reductions used to **normalize** the e-graph after
/// heap-producing ops (`fold`/`unfold`): the terminating `ite`/optional
/// simplifications (which peel the `(perm>0) ? Some(v) : None` wrapper down to
/// `v` whenever the permission is statically positive). The registry's ADT
/// reductions (which collapse `cons(proj(cons(..)))` snapshot towers) are
/// appended by `VerifyContext::new`. Kept separate from [`rules`] so that future
/// *non-terminating* rules are run only during full saturation, never here.
pub fn reduce_rules() -> Vec<Rule> {
    terminating_ite_rules()
}

/// Build the projection reduction `accessor(ctor(a0..an)) ⇒ a_index` for a
/// single (possibly verifier-synthesised, e.g. monomorphic) member id. Lets the
/// verifier register reductions for member ids minted after `VerifyContext`
/// construction (monomorphic Option instances).
pub fn proj_rule(accessor: FuncId, ctor: FuncId, index: usize) -> Rule {
    Rewrite::new(
        format!("proj-{}", accessor.0),
        UnaryAppSearcher { func: accessor },
        ProjApplier { ctor, index },
    )
    .expect("valid proj rewrite")
}

/// Build the discriminator reduction `tag_fn(ctor_C(..)) ⇒ index_C` for a single
/// (possibly synthesised) tag function. Companion to [`proj_rule`].
pub fn tag_rule(tag_fn: FuncId, ctor_tags: HashMap<FuncId, usize>) -> Rule {
    Rewrite::new(
        format!("tag-{}", tag_fn.0),
        UnaryAppSearcher { func: tag_fn },
        TagApplier { ctor_tags },
    )
    .expect("valid tag rewrite")
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
        // (c ? x : y) < z  =>  c ? (x < z) : (y < z)
        //
        // Distributes a comparison over a gated value. CFG linearization encodes
        // a conditional inhale/exhale as a *scaled permission* `c ? p : 0` rather
        // than a path condition, so the permission ≥ 0 obligation of such an
        // instruction is a `<` applied to an `ite`. Pushing the `<` inward lets
        // `ConstFold` decide each branch, after which `ite-same` collapses the
        // result. Terminating: strictly reduces the `ite` nesting above the `<`.
        rw!("lt-ite"; "(< (ite ?c ?x ?y) ?z)" => "(ite ?c (< ?x ?z) (< ?y ?z))"),
        // x == x => true   (reflexivity; also fires when congruence has already
        // merged the two operands into one e-class, e.g. a return var copied from
        // a param: `ensures r == a` after `r := a`).
        rw!("eq-refl"; "(== ?x ?x)" => "true"),
        // (a == b) proven true  =>  a ≡ b   (congruence)
        rw!("eq-true-union"; "(== ?a ?b)" => {
            UnionEqArgs { a: var("?a"), b: var("?b") }
        }),
        // (a && b) proven true  =>  a and b are each true.
        // `a && b` is `a ? b : false`; when that e-class is `true`, both
        // conjuncts hold (e.g. `assume a && b` lets `assert a` / `assert b`).
        rw!("and-true-decompose"; "(ite ?a ?b false)" => {
            AndTrueDecompose { a: var("?a"), b: var("?b") }
        }),
    ]);
    rules
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
fn terminating_ite_rules() -> Vec<Rule> {
    vec![
        // ite(true, x, y) => x
        rw!("ite-true";  "(ite true ?x ?y)"  => "?x"),
        // ite(false, x, y) => y
        rw!("ite-false"; "(ite false ?x ?y)" => "?y"),
        // c ? x : x  =>  x
        rw!("ite-same"; "(ite ?c ?x ?x)" => "?x"),
        // b && true  == b || false  == c ? true : false => c
        rw!("ite-ident"; "(ite ?c true false)" => "?c"),
        // b && b  ==  c ? c : false => c
        rw!("and-self";  "(ite ?c ?c false)" => "?c"),
        // b || b  ==  c ? true : c => c
        rw!("or-self";   "(ite ?c true ?c)" => "?c"),
        // c ? c : true  =>  true   (If c is true, it's true. If c is false, it's true)
        rw!("ite-c-true"; "(ite ?c ?c true)" => "true"),
        // c ? false : c =>  false  (If c is true, it's false. If c is false, it's false)
        rw!("ite-false-c"; "(ite ?c false ?c)" => "false"),
        // c ? (c ? x : y) : x  =>  x
        rw!("ite-nested-x-t"; "(ite ?c (ite ?c ?x ?y) ?x)" => "?x"),
        // c ? x : (c ? y : x)  =>  x
        rw!("ite-nested-x-f"; "(ite ?c ?x (ite ?c ?y ?x))" => "?x"),
        // c ? (c ? x : y) : y  =>  c ? x : y  (Merges outer root directly to inner node)
        rw!("ite-collapse-t"; "(ite ?c (ite ?c ?x ?y) ?y)" => "(ite ?c ?x ?y)"),
        // c ? x : (c ? x : y)  =>  c ? x : y  (Merges outer root directly to inner node)
        rw!("ite-collapse-f"; "(ite ?c ?x (ite ?c ?x ?y))" => "(ite ?c ?x ?y)"),
    ]
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

/// Applier for `and-true-decompose`: when a matched `a ? b : false` (i.e.
/// `a && b`) e-class is proven `true`, both conjuncts must be true, so union
/// each with the `true` literal. Sound and size-bounded (one shared literal).
struct AndTrueDecompose {
    a: Var,
    b: Var,
}

impl Applier<Symbolic, ConstFold> for AndTrueDecompose {
    fn apply_one(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<Symbolic>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        if !matches!(egraph[eclass].data.known(), Some(Literal::Bool(true))) {
            return vec![];
        }
        let true_ = egraph.add(Symbolic::Lit(Literal::Bool(true)));
        let mut changed = Vec::new();
        for v in [self.a, self.b] {
            let id = subst[v];
            if egraph.union(id, true_) {
                changed.push(egraph.find(id));
            }
        }
        changed
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

// ---- Generic domain axioms ("forall over types") --------------------------

/// A pure step of a prepared axiom body. Mirrors the `PureInst` subset legal in
/// an axiom, with every callee resolved to its verifier `FuncId` up front (the
/// applier has no registry access) and types still mentioning the axiom's
/// `Generic(i)` parameters — substituted per instantiation.
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

/// One instruction of a prepared axiom body: a value-producing pure step, or an
/// assumption (stitched from a callee's `#ensures`) merged with `true`.
pub(crate) enum AxiomInst {
    Val(AxiomPure),
    Assume(Val),
}

/// A generic domain axiom prepared for lazy instantiation: the body as
/// registry-resolved pure steps, its boolean result, and the **trigger** — the
/// one function application whose `type_args` cover all `n_params` type
/// parameters, so a ground application of it determines σ for the whole
/// (closed) axiom.
pub(crate) struct PreparedAxiom {
    pub n_params: usize,
    pub trigger_func: FuncId,
    /// The trigger's declared (generic) `type_args` — the pattern matched
    /// against a ground application's payload to extract σ.
    pub trigger_type_args: Vec<Type>,
    pub insts: Vec<AxiomInst>,
    pub res: Val,
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

/// Applier: for each ground application of the trigger in the matched e-class,
/// extract σ from its type payload, instantiate the whole axiom body at σ, and
/// merge its boolean with `true`. Memoized per σ (instantiation is idempotent —
/// re-adding hash-conses and re-unioning no-ops — so the memo is purely a
/// saturation-cost guard). Axiom bodies are never verified: no obligations.
/// Add a prepared body (of an axiom or a quantifier) to the e-graph, seeding
/// the value slots with `vals_seed` (the bound-variable σ for a quantifier;
/// empty for a closed axiom) and substituting `type_sigma` into every type
/// argument (the type-parameter σ for a generic axiom; empty for a quantifier).
/// Runs the body's `Assume`s (merging each with `true`) and returns the changed
/// e-classes together with the body's `res` e-class id. The caller decides how
/// to discharge `res` (an axiom merges it with `true`; a quantifier guards it).
fn build_instance(
    egraph: &mut EGraph<Symbolic, ConstFold>,
    insts: &[AxiomInst],
    res: &Val,
    vals_seed: &[Id],
    type_sigma: &[Type],
    changed: &mut Vec<Id>,
) -> Id {
    let mut vals: Vec<Id> = vals_seed.to_vec();
    fn get(egraph: &mut EGraph<Symbolic, ConstFold>, vals: &[Id], v: &Val) -> Id {
        match v {
            Val::Temp(n) => vals[*n],
            Val::Literal(lit) => egraph.add(Symbolic::Lit(lit.clone())),
        }
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
                        let tys: Box<[Type]> = type_args
                            .iter()
                            .map(|t| t.subst_generics(type_sigma))
                            .collect();
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
        }
    }
    get(egraph, &vals, res)
}

struct AxiomApplier {
    axiom: PreparedAxiom,
    memo: Mutex<HashSet<Vec<Type>>>,
}

impl AxiomApplier {
    /// Add the axiom body instantiated at `sigma` and merge `res` with `true`.
    /// Returns the e-classes changed by the unions.
    fn instantiate(&self, egraph: &mut EGraph<Symbolic, ConstFold>, sigma: &[Type]) -> Vec<Id> {
        let mut changed = Vec::new();
        let res = build_instance(
            egraph,
            &self.axiom.insts,
            &self.axiom.res,
            &[],
            sigma,
            &mut changed,
        );
        let true_ = egraph.add(Symbolic::Lit(Literal::Bool(true)));
        if egraph.union(res, true_) {
            changed.push(egraph.find(res));
        }
        changed
    }
}

impl Applier<Symbolic, ConstFold> for AxiomApplier {
    fn apply_one(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        eclass: Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<Symbolic>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        // Extract every distinct ground σ this e-class's trigger applications
        // determine. Collected first: `instantiate` needs `&mut egraph`.
        let mut sigmas: Vec<Vec<Type>> = Vec::new();
        for node in &egraph[eclass].nodes {
            let Symbolic::FuncApp(f, tys, _) = node else {
                continue;
            };
            if *f != self.axiom.trigger_func || tys.len() != self.axiom.trigger_type_args.len() {
                continue;
            }
            let mut sigma: Vec<Option<Type>> = vec![None; self.axiom.n_params];
            let matched = self
                .axiom
                .trigger_type_args
                .iter()
                .zip(tys.iter())
                .all(|(pat, ground)| pat.match_generics(ground, &mut sigma));
            if !matched {
                continue;
            }
            let Some(sigma): Option<Vec<Type>> = sigma.into_iter().collect() else {
                continue;
            };
            let mut memo = self.memo.lock().unwrap();
            if memo.insert(sigma.clone()) {
                sigmas.push(sigma);
            }
        }
        let mut changed = Vec::new();
        for sigma in sigmas {
            changed.extend(self.instantiate(egraph, &sigma));
        }
        changed
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// Mint the lazy-instantiation rule for one prepared generic axiom.
pub(crate) fn axiom_rule(name: &str, axiom: PreparedAxiom) -> Rule {
    let searcher = AxiomTriggerSearcher {
        func: axiom.trigger_func,
    };
    let applier = AxiomApplier {
        axiom,
        memo: Mutex::new(HashSet::new()),
    };
    Rewrite::new(format!("axiom-{name}"), searcher, applier).expect("axiom rule")
}

// ---- Pure `forall` quantifiers (value-σ triggered) -------------------------

/// A pure `forall` prepared for lazy instantiation: its opaque occurrence
/// function (`quant_func`), the capture and bound-variable arities, the trigger
/// function whose ground applications drive instantiation, the positional
/// trigger-argument map (`trig_args[k]` = the bound variable that trigger
/// argument `k` binds, or the capture param it must equal), and the body
/// (registry-resolved pure steps + boolean `res`, with temps `0..n_caps` the
/// captures and `n_caps..n_caps+n_bound` the binders). Unlike a generic axiom,
/// σ is over *values* (e-class ids read off the trigger's arguments), not
/// types.
pub(crate) struct PreparedQuantifier {
    pub quant_func: FuncId,
    pub n_caps: usize,
    pub n_bound: usize,
    pub trigger_func: FuncId,
    pub trig_args: Box<[TrigArg]>,
    pub insts: Vec<AxiomInst>,
    pub res: Val,
}

/// Applier: pair every ground occurrence `Q(c..)` in the e-graph with every
/// ground application of the trigger in the matched e-class whose capture
/// positions match the occurrence's capture args; read the bound-variable σ off
/// the binder positions, instantiate the body at `caps ++ σ`, and add the
/// **guarded** clause `Ite(Q(c..), res[c,σ], true) == true`. The instance is
/// released only once that ground occurrence merges `true` (existing
/// `ite(true, t, e) = t` rule), so instantiation is sound regardless of the
/// quantifier's truth. Occurrences are never created here — a top-level
/// (nullary) occurrence is added by the eager ground-axiom evaluation, a nested
/// one by an outer instance's `build_instance`; an unmaterialized quantifier is
/// correctly never instantiated (its guard could never fire). Memoized per
/// `caps ++ σ` (canonicalized at insert) — a saturation-cost guard, since
/// instantiation is idempotent.
struct QuantApplier {
    quant: PreparedQuantifier,
    memo: Mutex<HashSet<Vec<Id>>>,
}

impl Applier<Symbolic, ConstFold> for QuantApplier {
    fn apply_one(
        &self,
        egraph: &mut EGraph<Symbolic, ConstFold>,
        eclass: Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<Symbolic>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        // Enumerate the ground occurrences of this quantifier currently in the
        // e-graph. Distinct capture tuples in one e-class are distinct
        // occurrences (each yields its own instance); the guard condition is
        // the occurrence's e-class either way.
        let mut occurrences: Vec<(Id, Box<[Id]>)> = Vec::new();
        if let Some(classes) = egraph.classes_for_op(&Discriminant::FuncApp(self.quant.quant_func))
        {
            for occ_class in classes {
                for node in &egraph[occ_class].nodes {
                    let Symbolic::FuncApp(f, _, caps) = node else {
                        continue;
                    };
                    if *f == self.quant.quant_func && caps.len() == self.quant.n_caps {
                        occurrences.push((occ_class, caps.clone()));
                    }
                }
            }
        }
        // Pair each trigger application in the matched e-class with each
        // occurrence. Collected first: `build_instance` needs `&mut egraph`.
        let mut instances: Vec<(Id, Vec<Id>)> = Vec::new();
        for node in &egraph[eclass].nodes {
            let Symbolic::FuncApp(f, _, args) = node else {
                continue;
            };
            if *f != self.quant.trigger_func || args.len() != self.quant.trig_args.len() {
                continue;
            }
            for (occ_id, caps) in &occurrences {
                // Positional match: a `Bound(i)` argument defines σ(i) (a
                // repeated binder must land on the same e-class); a
                // `Capture(c)` argument must equal the occurrence's capture.
                let mut sigma: Vec<Option<Id>> = vec![None; self.quant.n_bound];
                let mut ok = true;
                for (k, &arg) in args.iter().enumerate() {
                    match self.quant.trig_args[k] {
                        TrigArg::Bound(i) => match &mut sigma[i] {
                            Some(prev) if egraph.find(*prev) != egraph.find(arg) => {
                                ok = false;
                                break;
                            }
                            slot => *slot = Some(egraph.find(arg)),
                        },
                        TrigArg::Capture(c) => {
                            if egraph.find(caps[c]) != egraph.find(arg) {
                                ok = false;
                                break;
                            }
                        }
                    }
                }
                if !ok {
                    continue;
                }
                let Some(sigma): Option<Vec<Id>> = sigma.into_iter().collect() else {
                    continue;
                };
                // The seed is the body's leading temps: captures then binders.
                let mut vals: Vec<Id> = caps.iter().map(|&c| egraph.find(c)).collect();
                vals.extend(sigma);
                // The capture tuple determines the instance, so the memo key
                // needs no occurrence-class component (the memo is per
                // quantifier already).
                let mut memo = self.memo.lock().unwrap();
                if memo.insert(vals.clone()) {
                    instances.push((*occ_id, vals));
                }
            }
        }
        let mut changed = Vec::new();
        for (occ_id, vals) in instances {
            let res = build_instance(
                egraph,
                &self.quant.insts,
                &self.quant.res,
                &vals,
                &[],
                &mut changed,
            );
            let true_ = egraph.add(Symbolic::Lit(Literal::Bool(true)));
            let guard = egraph.add(Symbolic::Ite([occ_id, res, true_]));
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

/// Mint the lazy-instantiation rule for one prepared pure `forall`.
pub(crate) fn quantifier_rule(name: &str, quant: PreparedQuantifier) -> Rule {
    let searcher = AxiomTriggerSearcher {
        func: quant.trigger_func,
    };
    let applier = QuantApplier {
        quant,
        memo: Mutex::new(HashSet::new()),
    };
    Rewrite::new(format!("quantifier-{name}"), searcher, applier).expect("quantifier rule")
}

// ---- Function-call unfolding (lazy, rewrite-rule triggered) ---------------

/// Applier: for each ground `FuncApp(self.func, _, args)` node in the matched
/// e-class, transplant the certificate's (unsaturated) body under `params →
/// args` and union it with the matched e-class — installing the definitional
/// equality `f(args) == body` lazily, the moment an occurrence is seen during
/// saturation, instead of eagerly at translation-walk time. Works uniformly
/// for a heap-free or heap-dependent `f`: by the time `cert` was captured, its
/// body's `Deref`/`Snap`/`FromSnap` were already resolved into ordinary
/// (pure) e-graph terms over the params — the certificate itself carries no
/// notion of "heap". Memoized per canonicalized arg tuple (a saturation-cost
/// guard, like `AxiomApplier`/`QuantApplier` — transplanting is idempotent, so
/// this only prevents re-walking the body every iteration).
struct FunctionUnfoldApplier {
    func: FuncId,
    cert: Arc<FunctionCertificate>,
    fresh_counter: Arc<Mutex<u32>>,
    memo: Mutex<HashSet<Vec<Id>>>,
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
        let mut calls: Vec<Vec<Id>> = Vec::new();
        for node in &egraph[eclass].nodes {
            let Symbolic::FuncApp(f, _, args) = node else {
                continue;
            };
            if *f != self.func {
                continue;
            }
            let args: Vec<Id> = args.iter().map(|&a| egraph.find(a)).collect();
            let mut memo = self.memo.lock().unwrap();
            if memo.insert(args.clone()) {
                calls.push(args);
            }
        }
        let mut changed = Vec::new();
        for args in calls {
            let mut subst: HashMap<Id, Id> = HashMap::new();
            for (p, a) in self.cert.params.iter().zip(&args) {
                subst.insert(self.cert.egraph.find(*p), *a);
            }
            let mut memo: HashMap<Id, Transplanted> = HashMap::new();
            let src = self.cert.src();
            let mut sink: Option<&mut TransplantSink<'_>> = None;
            let result = transplant(
                egraph,
                &self.fresh_counter,
                &mut sink,
                &src,
                self.cert.result,
                &subst,
                &mut memo,
            );
            if egraph.union(eclass, result) {
                changed.push(egraph.find(eclass));
            }
        }
        changed
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// Mint the lazy-unfolding rule for one verified function's certificate.
/// Reuses [`AxiomTriggerSearcher`] as-is — it only checks `FuncApp(f, ..)`
/// presence, independent of arity/type-args, exactly what's needed here too.
pub(crate) fn function_rule(
    name: &str,
    func: FuncId,
    cert: Arc<FunctionCertificate>,
    fresh_counter: Arc<Mutex<u32>>,
) -> Rule {
    let searcher = AxiomTriggerSearcher { func };
    let applier = FunctionUnfoldApplier {
        func,
        cert,
        fresh_counter,
        memo: Mutex::new(HashSet::new()),
    };
    Rewrite::new(format!("fn-{name}"), searcher, applier).expect("function rule")
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
