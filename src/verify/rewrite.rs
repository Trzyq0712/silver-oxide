//! Structural egg rewrite rules for the verifier.
//!
//! Only size-non-increasing rules live here: every RHS is a bare pattern
//! variable (a sub-term of the LHS), so applying a rule never builds a larger
//! term and the e-graph cannot grow exponentially. No
//! commutativity/associativity rules.
//!
//! `Symbolic` is a hand-written `Language` without `FromOp`, so the string
//! `rewrite!` macro is unavailable; patterns are built programmatically via
//! `PatternAst`/`ENodeOrVar` instead.

use egg::{ENodeOrVar, Pattern, PatternAst, Rewrite, Var};

use crate::verify::analysis::ConstFold;
use crate::verify::lang::Symbolic;
use crate::vmir::{BinOp, Literal, Type};

type Rule = Rewrite<Symbolic, ConstFold>;

fn var(name: &str) -> Var {
    name.parse().expect("valid pattern var")
}

/// The full rule set run during saturation.
pub fn rules() -> Vec<Rule> {
    let mut rules = vec![ite_true(), ite_false()];
    rules.extend(add_zero(Type::Int, Literal::Int(0.into())));
    rules.extend(add_zero(Type::Real, Literal::Real(num::BigInt::from(0).into())));
    rules
}

/// `ite(true, x, y) => x`. The `Ite` result type is irrelevant (ignored by
/// `Symbolic::matches`), so one rule covers every type.
fn ite_true() -> Rule {
    let x = var("?x");
    let y = var("?y");
    let mut lhs = PatternAst::default();
    let cond = lhs.add(ENodeOrVar::ENode(Symbolic::Lit(Literal::Bool(true))));
    let xn = lhs.add(ENodeOrVar::Var(x));
    let yn = lhs.add(ENodeOrVar::Var(y));
    lhs.add(ENodeOrVar::ENode(Symbolic::Ite(Type::Bool, [cond, xn, yn])));

    let mut rhs = PatternAst::default();
    rhs.add(ENodeOrVar::Var(x));

    Rewrite::new("ite-true", Pattern::new(lhs), Pattern::new(rhs)).unwrap()
}

/// `ite(false, x, y) => y`.
fn ite_false() -> Rule {
    let x = var("?x");
    let y = var("?y");
    let mut lhs = PatternAst::default();
    let cond = lhs.add(ENodeOrVar::ENode(Symbolic::Lit(Literal::Bool(false))));
    let xn = lhs.add(ENodeOrVar::Var(x));
    let yn = lhs.add(ENodeOrVar::Var(y));
    lhs.add(ENodeOrVar::ENode(Symbolic::Ite(Type::Bool, [cond, xn, yn])));

    let mut rhs = PatternAst::default();
    rhs.add(ENodeOrVar::Var(y));

    Rewrite::new("ite-false", Pattern::new(lhs), Pattern::new(rhs)).unwrap()
}

/// `x + 0 => x` and `0 + x => x` for the given numeric type. Type-correctness
/// is preserved by the concrete typed zero literal even though `Binary`'s
/// result type is ignored by matching.
fn add_zero(ty: Type, zero: Literal) -> Vec<Rule> {
    let make = |name: &str, swap: bool| {
        let x = var("?x");
        let mut lhs = PatternAst::default();
        let xn = lhs.add(ENodeOrVar::Var(x));
        let zn = lhs.add(ENodeOrVar::ENode(Symbolic::Lit(zero.clone())));
        let children = if swap { [zn, xn] } else { [xn, zn] };
        lhs.add(ENodeOrVar::ENode(Symbolic::Binary(BinOp::Plus, ty.clone(), children)));

        let mut rhs = PatternAst::default();
        rhs.add(ENodeOrVar::Var(x));

        Rewrite::new(name.to_string(), Pattern::new(lhs), Pattern::new(rhs)).unwrap()
    };
    let suffix = match ty {
        Type::Int => "int",
        Type::Real => "real",
        _ => "num",
    };
    vec![
        make(&format!("add-zero-{suffix}-r"), false),
        make(&format!("add-zero-{suffix}-l"), true),
    ]
}
