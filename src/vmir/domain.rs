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

/// A pure `forall` occurrence, lowered from an axiom body. The enclosing axiom
/// body references it as an opaque nullary boolean `FunctionCall` to this
/// declaration's own id (`{axiom}#quant{j}`); this declaration carries the
/// quantifier's body + trigger so the verifier can instantiate it lazily.
///
/// The `body` is a pure, heap-free inst stream whose `res` is the quantified
/// boolean, with the bound variables occupying `Val::Temp(0..bound.len())`
/// (closed — v1 forbids free value variables, so there are no leading capture
/// params yet). Like an axiom, a quantifier body is **never verified**; it only
/// contributes a lazy-instantiation rule. Instantiation at a ground trigger
/// application `f(t)` adds the guarded clause `Ite(occurrence, res[σ], true)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Quantifier {
    pub name: Spur,
    /// The binder types; body params are `Val::Temp(0..bound.len())`.
    pub bound: Box<[crate::vmir::Type]>,
    pub trigger: QuantTrigger,
    pub body: FunctionBody,
}

/// A quantifier's trigger: one function application whose arguments are exactly
/// the bound variables (each occurring once or repeated), jointly covering all
/// binders. Argument `k` of the application binds bound variable `binders[k]`,
/// so a ground application `f(t0, t1, ..)` determines σ = { binders[k] ↦ tk }.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct QuantTrigger {
    pub function: crate::vmir::MemberId,
    pub binders: Box<[usize]>,
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
        // The occurrence is a callable nullary boolean — `()` marks it (and is
        // where captured value parameters would appear once captures land).
        // Binders occupy `Val::Temp(0..bound.len())`, i.e. `e0..e{n-1}` — the
        // same variable syntax the body uses to reference them; their types are
        // written out.
        write!(f, "quantifier {name}() forall ")?;
        for (k, ty) in self.item.bound.iter().enumerate() {
            if k > 0 {
                write!(f, ", ")?;
            }
            write!(f, "e{k}: {}", self.with(ty))?;
        }
        write!(f, " :: {{{}(", trigger_fn)?;
        for (k, b) in self.item.trigger.binders.iter().enumerate() {
            if k > 0 {
                write!(f, ", ")?;
            }
            write!(f, "e{b}")?;
        }
        writeln!(f, ")}} {{")?;
        // The body's own temps (and the display counter) start after the
        // binders.
        write!(
            f,
            "{}",
            self.with((self.item.bound.len(), 0usize, &self.item.body.insts[..]))
        )?;
        writeln!(f, "  result: {}", self.item.body.res)?;
        write!(f, "}}")
    }
}
