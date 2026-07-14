use crate::vmir::display::VmirDisplay;
use crate::vmir::{FunctionBody, Type, Val};
use std::fmt::{self, Display, Formatter};

/// A pure `forall`, **inline** in the enclosing instruction stream (it is an
/// ordinary [`PureInst`](crate::vmir::PureInst) producing a `Bool`, not a
/// declaration). Closure-converted: `captures` are values of the *enclosing*
/// temp space — every outer-scope term the body or the triggers mention — and
/// the body reads them back as its own leading temps.
///
/// The body is a pure, heap-free inst stream whose `res` is the quantified
/// boolean. Its temps are the captures (`Val::Temp(0..captures.len())`), then
/// the binders (`Temp(n_caps..n_caps + bound.len())`), then its own steps.
///
/// Nesting needs no extra mechanism: an inner `forall` is a `PureInst::Forall`
/// inside the outer's body, and its `captures` are outer-body `Val`s (the outer
/// binders and captures). The verifier encodes a `forall` as a single e-node
/// whose payload is its compiled body ("recipe") and whose children are the
/// capture e-classes, so an outer instantiation materializes the inner
/// quantifier with the outer σ baked into the children.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Forall {
    /// The captured enclosing values, in the enclosing temp space. They occupy
    /// the body's leading temps.
    pub captures: Vec<Val>,
    /// The types of `captures`, positionally.
    pub cap_types: Box<[Type]>,
    /// The binder types; they occupy `Val::Temp(captures.len()..)`.
    pub bound: Box<[Type]>,
    /// The trigger groups, in source order — **alternatives**: a match of *any*
    /// one of them instantiates the quantifier. Never empty and never inferred:
    /// a `forall` without a usable trigger is a type error.
    pub triggers: Box<[QuantTrigger]>,
    pub body: FunctionBody,
}

/// One trigger group — a conjunctive multi-pattern (`{f(x), g(x)}`): the
/// quantifier instantiates at a σ only when **every** term matches. Each term's
/// root is an application ([`TrigTerm::App`]), and the group's `Bound` positions
/// jointly cover all binders (typecheck-enforced; repeats allowed).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct QuantTrigger {
    pub terms: Box<[TrigTerm]>,
}

/// A trigger pattern term. Matching it against a ground e-class, at a ground
/// `forall` node: a `Bound(i)` position determines σ(i) = the matched class, a
/// `Capture(j)` position requires that class to equal the node's `j`-th capture
/// child, a `Lit` requires the literal, and an `App` requires an application of
/// that head whose arguments recursively match — so a trigger may nest
/// arbitrarily (`{f(g(x), c)}`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TrigTerm {
    Bound(usize),
    Capture(usize),
    Lit(crate::vmir::Literal),
    App {
        head: TrigHead,
        type_args: Vec<Type>,
        args: Box<[TrigTerm]>,
    },
}

/// The head of a trigger application — the same heads a body's `PureInst` can
/// produce, so a trigger matches exactly what the program can build.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TrigHead {
    Func(crate::vmir::MemberId),
    AdtCons {
        adt: crate::vmir::MemberId,
        variant: usize,
    },
    AdtProj {
        adt: crate::vmir::MemberId,
        variant: usize,
        field: usize,
    },
    AdtTag {
        adt: crate::vmir::MemberId,
    },
}

/// A trigger term, rendered against the enclosing quantifier's capture arity
/// (`n_caps`): a capture prints as `e{c}`, a binder as `e{n_caps + i}` — the same
/// variable syntax the body uses.
impl<'a> Display for VmirDisplay<'a, (usize, &'a TrigTerm)> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let (n_caps, term) = self.item;
        match term {
            TrigTerm::Bound(i) => write!(f, "e{}", n_caps + i),
            TrigTerm::Capture(c) => write!(f, "e{c}"),
            TrigTerm::Lit(lit) => write!(f, "{lit}"),
            TrigTerm::App {
                head,
                type_args,
                args,
            } => {
                match head {
                    TrigHead::Func(id) => write!(f, "{}", self.member(*id))?,
                    TrigHead::AdtCons { adt, variant } => {
                        write!(f, "{}", self.adt_variant(*adt, *variant))?
                    }
                    TrigHead::AdtProj {
                        adt,
                        variant,
                        field,
                    } => write!(f, "{}.{field}", self.adt_variant(*adt, *variant))?,
                    TrigHead::AdtTag { adt } => write!(f, "{}@tag", self.member(*adt))?,
                }
                if !type_args.is_empty() {
                    write!(f, "<")?;
                    for (i, t) in type_args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", self.with(t))?;
                    }
                    write!(f, ">")?;
                }
                write!(f, "(")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", self.with((n_caps, a)))?;
                }
                write!(f, ")")
            }
        }
    }
}

/// An inline `forall`, rendered as a nested block:
///
/// ```text
///   e4: Bool := forall(e0 := e1) e1: Int :: {f(e1)} {
///     e2: Bool := f(e1)
///     result: e2
///   }
/// ```
///
/// The capture bindings map the body's leading temps (`e0..`) to the values they
/// take in the *enclosing* space; the binders continue the body's numbering.
impl<'a> Display for VmirDisplay<'a, &'a Forall> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let q = self.item;
        let n_caps = q.captures.len();
        write!(f, "forall(")?;
        for (k, (val, ty)) in q.captures.iter().zip(q.cap_types.iter()).enumerate() {
            if k > 0 {
                write!(f, ", ")?;
            }
            write!(f, "e{k}: {} := {val}", self.with(ty))?;
        }
        write!(f, ") ")?;
        for (k, ty) in q.bound.iter().enumerate() {
            if k > 0 {
                write!(f, ", ")?;
            }
            write!(f, "e{}: {}", n_caps + k, self.with(ty))?;
        }
        // Trigger groups, alternatives side by side: `{f(e1), g(e1)}{h(e1)}`.
        write!(f, " :: ")?;
        for group in q.triggers.iter() {
            write!(f, "{{")?;
            for (k, term) in group.terms.iter().enumerate() {
                if k > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", self.with((n_caps, term)))?;
            }
            write!(f, "}}")?;
        }
        writeln!(f, " {{")?;
        // The body's own temps continue after the captures and binders.
        write!(
            f,
            "{}",
            self.with((n_caps + q.bound.len(), 0usize, &q.body.insts[..]))
        )?;
        writeln!(f, "  result: {}", q.body.res)?;
        write!(f, "  }}")
    }
}
