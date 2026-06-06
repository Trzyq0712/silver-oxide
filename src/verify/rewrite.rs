//! Structural egg rewrite rules for the verifier.

use egg::{Applier, EGraph, Id, PatternAst, Rewrite, Subst, Symbol, Var, rewrite as rw};

use crate::verify::analysis::ConstFold;
use crate::verify::lang::Symbolic;
use crate::vmir::Literal;

type Rule = Rewrite<Symbolic, ConstFold>;

fn var(name: &str) -> Var {
    name.parse().expect("valid pattern var")
}

/// The full rule set run during saturation.
pub fn rules() -> Vec<Rule> {
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
        // x + 0 => x  (Int)
        rw!("add-zero-int-r"; "(+ ?x 0)" => "?x"),
        rw!("add-zero-int-l"; "(+ 0 ?x)" => "?x"),
        // x + 0 => x  (Real zero literal `0/1`; `real(0)` const-folds to it)
        rw!("add-zero-real-r"; "(+ ?x 0/1)" => "?x"),
        rw!("add-zero-real-l"; "(+ 0/1 ?x)" => "?x"),
        // (a == b) proven true  =>  a ≡ b   (congruence)
        rw!("eq-true-union"; "(== ?a ?b)" => {
            UnionEqArgs { a: var("?a"), b: var("?b") }
        }),
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
