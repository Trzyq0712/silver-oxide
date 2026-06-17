//! Structural egg rewrite rules for the verifier.

use std::collections::HashMap;

use egg::{
    Applier, EGraph, Id, PatternAst, Rewrite, SearchMatches, Searcher, Subst, Symbol, Var,
    rewrite as rw,
};

use crate::verify::analysis::ConstFold;
use crate::verify::lang::Symbolic;
use crate::vmir::{AdtMeta, Literal, MemberId};

type Rule = Rewrite<Symbolic, ConstFold>;

fn var(name: &str) -> Var {
    name.parse().expect("valid pattern var")
}

/// The full rule set: the static structural rules plus per-ADT reductions
/// generated from `adt_meta` (currently the discriminator tag reduction).
pub fn rules(adt_meta: &AdtMeta) -> Vec<Rule> {
    let mut rules = static_rules();
    rules.extend(adt_rules(adt_meta));
    rules
}

/// The terminating structural reductions used to **normalize** the e-graph after
/// heap-producing ops (`fold`/`unfold`): the ADT reductions (which collapse the
/// `cons(proj(cons(..)))` snapshot towers) plus the terminating `ite`/optional
/// simplifications (which peel the `(perm>0) ? Some(v) : None` wrapper down to
/// `v` whenever the permission is statically positive). Kept separate from
/// [`rules`] so that future *non-terminating* rules (e.g. recursive function
/// defining-equations) are run only during full saturation, never here.
pub fn reduce_rules(adt_meta: &AdtMeta) -> Vec<Rule> {
    let mut rules = adt_rules(adt_meta);
    rules.extend(terminating_ite_rules());
    rules
}

/// Build the projection reduction `accessor(ctor(a0..an)) ⇒ a_index` for a
/// single (possibly verifier-synthesised, e.g. monomorphic) member id. Lets the
/// verifier register reductions for member ids minted after `VerifyContext`
/// construction (monomorphic Option instances).
pub fn proj_rule(accessor: MemberId, ctor: MemberId, index: usize) -> Rule {
    Rewrite::new(
        format!("proj-{}", usize::from(accessor)),
        UnaryAppSearcher { func: accessor },
        ProjApplier { ctor, index },
    )
    .expect("valid proj rewrite")
}

/// Build the discriminator reduction `tag_fn(ctor_C(..)) ⇒ index_C` for a single
/// (possibly synthesised) tag function. Companion to [`proj_rule`].
pub fn tag_rule(tag_fn: MemberId, ctor_tags: HashMap<MemberId, usize>) -> Rule {
    Rewrite::new(
        format!("tag-{}", usize::from(tag_fn)),
        UnaryAppSearcher { func: tag_fn },
        TagApplier { ctor_tags },
    )
    .expect("valid tag rewrite")
}

/// ADT reductions generated from `adt_meta`: the discriminator `tag` reduction
/// and the constructor-projection reduction. Both are terminating.
fn adt_rules(adt_meta: &AdtMeta) -> Vec<Rule> {
    let mut rules = Vec::new();
    for (&tag_fn, ctor_tags) in &adt_meta.tag_fns {
        // `Adt@tag(ctor_C(..)) ⇒ index_C`. FuncApp isn't string-matchable, so
        // both searcher and applier are custom.
        rules.push(
            Rewrite::new(
                format!("tag-{}", usize::from(tag_fn)),
                UnaryAppSearcher { func: tag_fn },
                TagApplier {
                    ctor_tags: ctor_tags.clone(),
                },
            )
            .expect("valid tag rewrite"),
        );
    }
    for (&accessor, &(ctor, index)) in &adt_meta.dtors {
        // `Adt@f(ctor_C(a0..an)) ⇒ a_index`.
        rules.push(
            Rewrite::new(
                format!("proj-{}", usize::from(accessor)),
                UnaryAppSearcher { func: accessor },
                ProjApplier { ctor, index },
            )
            .expect("valid proj rewrite"),
        );
    }
    rules
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
        // (a == b) proven true  =>  a ≡ b   (congruence)
        rw!("eq-true-union"; "(== ?a ?b)" => {
            UnionEqArgs { a: var("?a"), b: var("?b") }
        }),
    ]);
    rules
}

/// Terminating `ite` simplifications. Shared by the saturation rule set and the
/// post-`fold`/`unfold` reduction set. Under an assumed branch literal (on the
/// instruction's path condition) `ite-true`/`ite-false` reduce a gated
/// permission `b ? p : 0` to `p` (resp. `0`), which is what discharges a
/// conditional `acc`'s permission ≥ 0 obligation and peels the optional snapshot
/// member's discriminant — no comparison-over-`ite` distribution needed.
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
        // `ConstFold::merge` records as `data.value = Some(Bool(true))`.
        if egraph[eclass].data.value != Some(Literal::Bool(true)) {
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

/// Searcher for a unary application `func(?x)`: matches any
/// `FuncApp(func, [x])` node in an e-class and binds `?x` to the argument.
/// FuncApp isn't string-matchable, so this is hand-written. Shared by the tag
/// and projection reductions.
struct UnaryAppSearcher {
    func: MemberId,
}

impl Searcher<Symbolic, ConstFold> for UnaryAppSearcher {
    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<Symbolic, ConstFold>,
        eclass: Id,
        limit: usize,
    ) -> Option<SearchMatches<'_, Symbolic>> {
        let mut substs = Vec::new();
        for node in &egraph[eclass].nodes {
            if let Symbolic::FuncApp(f, args) = node
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
    ctor_tags: HashMap<MemberId, usize>,
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
            if let Symbolic::FuncApp(c, _) = node
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
/// constructor's `index`-th argument.
struct ProjApplier {
    ctor: MemberId,
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
            if let Symbolic::FuncApp(c, args) = node
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
