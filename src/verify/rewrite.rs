//! Structural egg rewrite rules for the verifier.
//!
//! Only size-non-increasing rules live here: every RHS is a bare pattern
//! variable (a sub-term of the LHS), so applying a rule never builds a larger
//! term and the e-graph cannot grow exponentially. No
//! commutativity/associativity rules.
//!
//! `Symbolic` is a hand-written, *typed* `Language` (nodes carry `Type` /
//! `MemberId`), so egg's string `rewrite!` macro — which needs `FromOp` — is
//! not used. Instead, rules are written declaratively via the small [`Pat`]
//! builder below: e.g. `rule("ite-true", pite(pbool(true), pvar("?x"),
//! pvar("?y")), pvar("?x"))`.

use egg::{Applier, EGraph, ENodeOrVar, Id, Pattern, PatternAst, Rewrite, Subst, Symbol, Var};

use crate::verify::analysis::ConstFold;
use crate::verify::lang::Symbolic;
use crate::vmir::{BinOp, Literal, Type};

type Rule = Rewrite<Symbolic, ConstFold>;

fn var(name: &str) -> Var {
    name.parse().expect("valid pattern var")
}

// ======================
// PATTERN BUILDER DSL
// ======================

/// A pattern term over [`Symbolic`], built declaratively and lowered to a
/// `PatternAst`. Mirrors the `Symbolic` variants that appear in rules; the
/// `Ite` result type is omitted because `Symbolic::matches` ignores it.
enum Pat {
    Var(&'static str),
    Lit(Literal),
    Binary(BinOp, Type, Box<Pat>, Box<Pat>),
    Ite(Box<Pat>, Box<Pat>, Box<Pat>),
}

impl Pat {
    fn build(&self, ast: &mut PatternAst<Symbolic>) -> Id {
        match self {
            Pat::Var(name) => ast.add(ENodeOrVar::Var(var(name))),
            Pat::Lit(lit) => ast.add(ENodeOrVar::ENode(Symbolic::Lit(lit.clone()))),
            Pat::Binary(op, ty, l, r) => {
                let l = l.build(ast);
                let r = r.build(ast);
                ast.add(ENodeOrVar::ENode(Symbolic::Binary(*op, ty.clone(), [l, r])))
            }
            Pat::Ite(c, t, e) => {
                let c = c.build(ast);
                let t = t.build(ast);
                let e = e.build(ast);
                // Result type is irrelevant to matching; `Bool` is a placeholder.
                ast.add(ENodeOrVar::ENode(Symbolic::Ite(Type::Bool, [c, t, e])))
            }
        }
    }

    fn pattern(&self) -> Pattern<Symbolic> {
        let mut ast = PatternAst::default();
        self.build(&mut ast);
        Pattern::new(ast)
    }
}

fn pvar(name: &'static str) -> Pat {
    Pat::Var(name)
}
fn pbool(b: bool) -> Pat {
    Pat::Lit(Literal::Bool(b))
}
fn pite(c: Pat, t: Pat, e: Pat) -> Pat {
    Pat::Ite(Box::new(c), Box::new(t), Box::new(e))
}
fn pbin(op: BinOp, ty: Type, l: Pat, r: Pat) -> Pat {
    Pat::Binary(op, ty, Box::new(l), Box::new(r))
}

/// A rewrite from one pattern to another (RHS is a sub-term of the LHS).
fn rule(name: &str, lhs: Pat, rhs: Pat) -> Rule {
    Rewrite::new(name.to_string(), lhs.pattern(), rhs.pattern()).unwrap()
}

/// A rewrite with a custom applier (e.g. a conditional e-class union).
fn rule_with(
    name: &str,
    lhs: Pat,
    applier: impl Applier<Symbolic, ConstFold> + Send + Sync + 'static,
) -> Rule {
    Rewrite::new(name.to_string(), lhs.pattern(), applier).unwrap()
}

// ======================
// RULE SET
// ======================

/// The full rule set run during saturation.
pub fn rules() -> Vec<Rule> {
    let mut rules = vec![
        // ite(true, x, y) => x   /   ite(false, x, y) => y
        rule("ite-true", pite(pbool(true), pvar("?x"), pvar("?y")), pvar("?x")),
        rule("ite-false", pite(pbool(false), pvar("?x"), pvar("?y")), pvar("?y")),
        // b && true  =  ite(b, true, false) => b
        rule(
            "ite-true-false",
            pite(pvar("?c"), pbool(true), pbool(false)),
            pvar("?c"),
        ),
        // b && b  =  ite(b, b, false) => b
        rule(
            "and-self",
            pite(pvar("?c"), pvar("?c"), pbool(false)),
            pvar("?c"),
        ),
        eq_true_union(),
    ];
    rules.extend(add_zero(Type::Int, Literal::Int(0.into())));
    rules.extend(add_zero(Type::Real, Literal::Real(num::BigInt::from(0).into())));
    rules
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

/// `(a == b) == true => a ≡ b`: propagate a proven equality into congruence by
/// unioning the operands. `Eq`'s result type is always `Bool`, so the concrete
/// type in the pattern is correct under type-comparing `Binary` matching.
fn eq_true_union() -> Rule {
    rule_with(
        "eq-true-union",
        pbin(BinOp::Eq, Type::Bool, pvar("?a"), pvar("?b")),
        UnionEqArgs {
            a: var("?a"),
            b: var("?b"),
        },
    )
}

/// `x + 0 => x` and `0 + x => x` for the given numeric type. Type-correctness
/// is preserved by the concrete typed zero literal even though `Binary`'s
/// result type is ignored by matching.
fn add_zero(ty: Type, zero: Literal) -> Vec<Rule> {
    let suffix = match ty {
        Type::Int => "int",
        Type::Real => "real",
        _ => "num",
    };
    let lit = || Pat::Lit(zero.clone());
    vec![
        rule(
            &format!("add-zero-{suffix}-r"),
            pbin(BinOp::Plus, ty.clone(), pvar("?x"), lit()),
            pvar("?x"),
        ),
        rule(
            &format!("add-zero-{suffix}-l"),
            pbin(BinOp::Plus, ty, lit(), pvar("?x")),
            pvar("?x"),
        ),
    ]
}
