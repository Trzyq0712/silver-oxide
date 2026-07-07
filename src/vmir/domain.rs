use crate::vmir::FunctionBody;
use crate::vmir::display::VmirDisplay;
use std::fmt::{self, Display, Formatter};

use lasso::Spur;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Domain {
    pub name: Spur,
    pub ty_params: TyParams,
}

/// A ground (quantifier-free) axiom: a closed boolean fact the verifier
/// **assumes** in every verification unit. In VMIR an axiom is a free-standing
/// declaration, not bound to a domain (Silver domains only supply the source
/// syntax). The body is a pure, heap-free inst stream (`Pure` + the `Assume`s
/// stitched from a callee's `#ensures`; no params, so `Val::Temp` counts from
/// 0) whose `res` is the axiom's boolean — merged with `true` before
/// verification. Axiom bodies are **never verified**: no well-definedness
/// obligations (div-by-zero etc.) are checked on them. A generic axiom
/// (`ty_params > 0`) holds for every ground instantiation of its type
/// parameters ("forall over types"); the verifier instantiates it lazily,
/// triggered by ground applications of the functions it mentions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Axiom {
    pub name: Option<Spur>,
    pub ty_params: TyParams,
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
/// Instantiation of a ground occurrence `Q(c..)` at a ground trigger
/// application `f(t..)` adds the guarded clause `Ite(Q(c..), res[c,σ], true)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Quantifier {
    pub name: Spur,
    /// The capture-parameter types; they occupy `Val::Temp(0..params.len())`.
    pub params: Box<[crate::vmir::Type]>,
    /// The binder types; they occupy `Val::Temp(params.len()..)` after the
    /// captures.
    pub bound: Box<[crate::vmir::Type]>,
    pub trigger: QuantTrigger,
    pub body: FunctionBody,
}

/// A quantifier's trigger: one function application whose arguments are each a
/// bound variable or a captured param, with the bound positions jointly
/// covering all binders (repeats allowed). At a ground occurrence `Q(c..)` and
/// a ground application `f(t0, t1, ..)`: an `args[k] = Bound(i)` position
/// determines σ(i) = tk, an `args[k] = Capture(j)` position requires tk = cj.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct QuantTrigger {
    pub function: crate::vmir::MemberId,
    pub args: Box<[TrigArg]>,
}

/// One argument position of a quantifier's trigger application: either a bound
/// variable (defines σ at that binder) or a capture param (must equal the
/// occurrence's capture argument).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrigArg {
    Bound(usize),
    Capture(usize),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TyParams(usize);

impl From<usize> for TyParams {
    fn from(n: usize) -> Self {
        Self(n)
    }
}

impl TyParams {
    /// The type-parameter arity.
    pub fn count(&self) -> usize {
        self.0
    }
}

impl Axiom {
    /// The axiom's **trigger**: the first `FunctionCall` in the body whose
    /// `type_args` mention all of the axiom's type parameters. A ground
    /// instantiation of that one application determines the instantiation of
    /// the whole (closed) axiom — the verifier reads σ off matched
    /// applications of it. `None` when the axiom is generic but no single call
    /// covers every parameter (rejected at translation); for a monomorphic
    /// axiom the first call (if any) trivially covers zero parameters.
    pub fn covering_trigger(&self) -> Option<&crate::vmir::FunctionCall> {
        let n = self.ty_params.count();
        self.body.insts.iter().find_map(|inst| {
            let crate::vmir::InstKind::Pure(_, crate::vmir::PureInst::FunctionCall(call)) =
                &inst.kind
            else {
                return None;
            };
            let mut seen = std::collections::HashSet::new();
            for ty in &call.type_args {
                ty.collect_generics(&mut seen);
            }
            (0..n).all(|i| seen.contains(&i)).then_some(call)
        })
    }
}

impl Display for TyParams {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // A declaration's generic parameters are positional (`Generic(n)` → `?n`),
        // so the binder only states the **arity** (`<2>`); the params are referred
        // to as `?0`, `?1`, … Angle brackets match type-argument instantiation
        // (`[..]` is reserved for heaps / addr groups). Nothing is printed for a
        // non-generic declaration.
        if self.0 == 0 {
            return Ok(());
        }
        write!(f, "<{}>", self.0)
    }
}

impl<'a> Display for VmirDisplay<'a, &'a Domain> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = self.interner.resolve(&self.item.name);
        let ty_params = &self.item.ty_params;
        writeln!(f, "domain {name}{ty_params}")
    }
}

impl<'a> Display for VmirDisplay<'a, &'a Axiom> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "axiom")?;
        if let Some(n) = &self.item.name {
            write!(f, " {}", self.interner.resolve(n))?;
        }
        write!(f, "{}", self.item.ty_params)?;
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

impl<'a> Display for VmirDisplay<'a, &'a Quantifier> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = self.interner.resolve(&self.item.name);
        let trigger_fn = self.member(self.item.trigger.function);
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
        write!(f, " :: {{{}(", trigger_fn)?;
        for (k, a) in self.item.trigger.args.iter().enumerate() {
            if k > 0 {
                write!(f, ", ")?;
            }
            match a {
                crate::vmir::TrigArg::Bound(i) => write!(f, "e{}", n_caps + i)?,
                crate::vmir::TrigArg::Capture(c) => write!(f, "e{c}")?,
            }
        }
        writeln!(f, ")}} {{")?;
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
