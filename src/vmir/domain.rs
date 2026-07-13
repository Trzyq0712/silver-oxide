use crate::vmir::FunctionBody;
use crate::vmir::display::VmirDisplay;
use std::fmt::{self, Display, Formatter};

use lasso::Spur;

/// A domain — a monomorphic namespace of uninterpreted functions. Generics live
/// on ADTs: a domain declaring type parameters is rejected at translation
/// (`GenericDomainUnsupported`), since instantiating its axioms would need a
/// *type* trigger, which Silver has no syntax to write.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Domain {
    pub name: Spur,
}

/// A ground (quantifier-free) axiom: a closed boolean fact the verifier
/// **assumes** in every verification unit. In VMIR an axiom is a free-standing
/// declaration, not bound to a domain (Silver domains only supply the source
/// syntax). The body is a pure, heap-free inst stream (`Pure` + the `Assume`s
/// stitched from a callee's `#ensures`; no params, so `Val::Temp` counts from
/// 0) whose `res` is the axiom's boolean — merged with `true` before
/// verification. Axiom bodies are **never verified**: no well-definedness
/// obligations (div-by-zero etc.) are checked on them. Quantification over
/// *values* is a `forall` in the body (a [`Quantifier`] occurrence); there is no
/// quantification over types.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Axiom {
    pub name: Option<Spur>,
    pub body: FunctionBody,
}

/// A pure `forall` occurrence, lowered from an axiom body. The enclosing body
/// (the axiom's, or an outer quantifier's) references it as an opaque boolean
/// `FunctionCall` to this declaration's own id (`{axiom}#quant{j}`) whose
/// arguments are the **captured** enclosing values, one per entry in `params`;
/// this declaration carries the quantifier's body + trigger so the verifier can
/// instantiate it lazily.
///
/// The `body` is a pure, heap-free inst stream whose `res` is the quantified
/// boolean. Its leading temps are the capture params (`Val::Temp(0..n_caps)`)
/// followed by the bound variables (`Temp(n_caps..n_caps + bound.len())`); the
/// body's own temps count from there. Like an axiom, a quantifier body is
/// **never verified**; it only contributes a lazy-instantiation rule.
/// Instantiation of a ground occurrence `Q(c..)` at a ground match of one
/// trigger group adds the guarded clause `Ite(Q(c..), res[c,σ], true)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Quantifier {
    pub name: Spur,
    /// The capture-parameter types; they occupy `Val::Temp(0..params.len())`.
    pub params: Box<[crate::vmir::Type]>,
    /// The binder types; they occupy `Val::Temp(params.len()..)` after the
    /// captures.
    pub bound: Box<[crate::vmir::Type]>,
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
/// occurrence `Q(c..)`: a `Bound(i)` position determines σ(i) = the matched
/// class, a `Capture(j)` position requires that class to equal `cj`, a `Lit`
/// requires the literal, and an `App` requires an application of that head whose
/// arguments recursively match — so a trigger may nest arbitrarily
/// (`{f(g(x), c)}`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TrigTerm {
    Bound(usize),
    Capture(usize),
    Lit(crate::vmir::Literal),
    App {
        head: TrigHead,
        type_args: Vec<crate::vmir::Type>,
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

impl<'a> Display for VmirDisplay<'a, &'a Domain> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = self.interner.resolve(&self.item.name);
        writeln!(f, "domain {name}")
    }
}

impl<'a> Display for VmirDisplay<'a, &'a Axiom> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "axiom")?;
        if let Some(n) = &self.item.name {
            write!(f, " {}", self.interner.resolve(n))?;
        }
        writeln!(f, " {{")?;
        write!(
            f,
            "{}",
            self.with((0usize, 0usize, &self.item.body.insts[..]))
        )?;
        writeln!(f, "  result: {}", self.item.body.res)?;
        write!(f, "}}")
    }
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

impl<'a> Display for VmirDisplay<'a, &'a Quantifier> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = self.interner.resolve(&self.item.name);
        let n_caps = self.item.params.len();
        // The occurrence is a callable boolean; the parens carry the capture
        // params. Captures occupy `Val::Temp(0..n_caps)` (`e0..`), binders
        // continue at `e{n_caps}` — the same variable syntax the body uses to
        // reference them; their types are written out.
        write!(f, "quantifier {name}(")?;
        for (k, ty) in self.item.params.iter().enumerate() {
            if k > 0 {
                write!(f, ", ")?;
            }
            write!(f, "e{k}: {}", self.with(ty))?;
        }
        write!(f, ") forall ")?;
        for (k, ty) in self.item.bound.iter().enumerate() {
            if k > 0 {
                write!(f, ", ")?;
            }
            write!(f, "e{}: {}", n_caps + k, self.with(ty))?;
        }
        // Trigger groups, alternatives side by side: `{f(e1), g(e1)}{h(e1)}`.
        write!(f, " :: ")?;
        for group in self.item.triggers.iter() {
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
        // The body's own temps (and the display counter) start after the
        // captures and binders.
        write!(
            f,
            "{}",
            self.with((
                n_caps + self.item.bound.len(),
                0usize,
                &self.item.body.insts[..]
            ))
        )?;
        writeln!(f, "  result: {}", self.item.body.res)?;
        write!(f, "}}")
    }
}
