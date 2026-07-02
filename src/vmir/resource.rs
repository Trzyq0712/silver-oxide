use crate::vmir::display::VmirDisplay;
use crate::vmir::{
    Adt, AdtVariant, Bound, Domain, Function, HeapInst, HeapVal, Inst, InstKind, MemberId, Type,
    Val,
};
use std::fmt::{self, Display, Formatter};
use lasso::Spur;

/// A reusable unit of proof.
///
/// A resource computes a heap delta and a boolean condition. Its address function
/// and snapshot type are not stored — they are mechanically implied by the
/// definition and derived on demand (the `@addr` function via
/// [`Resource::derive_location`]; the snapshot via [`Resource::derive_snapshot`]).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Resource {
    pub name: Spur,
    pub params: Vec<Type>,
    pub precond: Precond,
    pub body: Option<ResourceBody>,
}

/// A resource's precondition mode.
///
/// - `SelfFramed`: one-state — the body reads only its own footprint. Predicates,
///   `#requires`, and function preconditions. Snapshottable / foldable.
/// - `Ctx(req, args)`: two-state — the body additionally reads a context heap
///   (`HeapVal::Temp(0)`), the delta of the precondition resource `req` applied
///   to `args` (the caller-supplied pre-state). `#ensures`. Opaque-only; never
///   snapshotted or folded.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Precond {
    SelfFramed,
    Ctx(MemberId, Vec<Val>),
}

impl Resource {
    /// Whether the body reads only its own footprint (no ctx/pre-state heap).
    /// Only self-framed resources may be snapshotted / folded / unfolded.
    pub fn is_self_framed(&self) -> bool {
        matches!(self.precond, Precond::SelfFramed)
    }

    /// This resource's `@addr` **function**: `params -> &[group] Snap(id) @ *`.
    /// The address is a generic-`ADDR` application; all location metadata (group
    /// tag, snapshot value, unbounded permission) rides in the return type.
    /// Derived on demand — not emitted as a declaration. `group` is the predicate's
    /// interned group tag (`Program.groups`).
    pub fn derive_location(&self, id: MemberId, group: lasso::Spur) -> Function {
        Function {
            name: self.name,
            ty_params: 0.into(),
            params: self.params.clone().into(),
            ret: Type::addr(group, Type::Snap(id), Bound::Unbounded),
            precond: Precond::SelfFramed,
            body: None,
        }
    }

    /// Derive this resource's snapshot type (see [`Snapshot`]):
    /// - a concrete predicate → a single-constructor [`Adt`] over the footprint
    ///   slots, each typed `Option[T]` (a slot is present-or-absent — `fold` packs
    ///   `present ? Some(v) : None`);
    /// - an abstract (bodyless) predicate → an opaque empty [`Domain`].
    ///
    /// `None` for a non self-framed resource (two-state; no foldable snapshot).
    /// Not stored in the IR — the verifier mints the snapshot's
    /// constructor/projection ids from this on demand.
    ///
    /// Slot types come from the body: only `Pure` insts produce a `Val`, and
    /// params occupy `Val::Temp(0..n)`, so a `Val -> Type` map is just the params
    /// followed by each `Pure`'s result type. Every footprint slot is a
    /// `HeapInst::Combine` whose `loc` is an address of type `Addr<T>`; the slot
    /// type is `Option[T]`.
    pub fn derive_snapshot(&self) -> Option<Snapshot> {
        if !self.is_self_framed() {
            return None;
        }
        let Some(body) = &self.body else {
            return Some(Snapshot::Abstract(Domain {
                name: self.name,
                ty_params: 0.into(),
            }));
        };
        let mut val_types: Vec<Type> = self.params.clone();
        let mut field_types = Vec::new();
        for inst in &body.insts {
            match &inst.kind {
                InstKind::Pure(ty, _) => val_types.push(ty.clone()),
                InstKind::Heap(HeapInst::Combine { loc, .. }) => {
                    let ty = match loc {
                        Val::Temp(n) => val_types.get(*n),
                        Val::Literal(_) => None,
                    };
                    if let Some(Type::Addr { value, .. }) = ty {
                        field_types.push(Type::Option(value.clone()));
                    }
                }
                _ => {}
            }
        }
        Some(Snapshot::Concrete(Adt {
            name: self.name,
            ty_params: 0.into(),
            // A snapshot's single constructor is synthetic — no source name.
            variants: vec![AdtVariant {
                name: None,
                field_types,
            }],
        }))
    }
}

/// The derived snapshot type of a resource (see [`Resource::derive_snapshot`]):
/// a concrete predicate's is an [`Adt`] with a single constructor over the
/// `Option`-wrapped footprint slot types; an abstract predicate's is an opaque
/// empty [`Domain`]. Never stored in the IR.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Snapshot {
    Concrete(Adt),
    Abstract(Domain),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResourceBody {
    pub insts: Vec<Inst>,
    pub res: (HeapVal, Val),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResourceCall {
    pub resource: MemberId,
    /// The context heap, present only when the called resource has a
    /// precondition resource. `None` for self-framed (context-free) calls.
    pub ctx_heap: Option<HeapVal>,
    pub args: Vec<Val>,
}

// ======================
// DISPLAY INFRASTRUCTURE
// ======================

impl<'a> Display for VmirDisplay<'a, &'a Resource> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = self.interner.resolve(&self.item.name);
        write!(f, "resource {name}(")?;
        for (i, param) in self.item.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            // Params occupy `Val::Temp(0..n)`, so label them `e0`, `e1`, … to
            // match the temporaries the body refers to.
            write!(f, "e{i}: {}", self.with(param))?;
        }
        write!(f, ")")?;

        match &self.item.body {
            None => Ok(()),
            Some(body) => {
                // A self-framed resource has no precondition: print no `[..]`
                // annotation and count emitted heaps from `h0` (its initial heap
                // is `empty`). A two-state resource shows its context resource
                // `[req(args)]` and reserves `h0` for that ctx heap, so its body
                // heaps start at `h1`.
                let heap_base = match &self.item.precond {
                    Precond::SelfFramed => 0usize,
                    Precond::Ctx(req_id, req_args) => {
                        write!(f, "[{}(", self.member(*req_id))?;
                        for (i, arg) in req_args.iter().enumerate() {
                            if i > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{}", arg)?;
                        }
                        write!(f, ")]")?;
                        1usize
                    }
                };
                writeln!(f, " {{")?;
                write!(
                    f,
                    "{}",
                    self.with((self.item.params.len(), heap_base, &body.insts[..]))
                )?;
                writeln!(f, "  result: ({}, {})", body.res.0, body.res.1)?;
                write!(f, "}}")
            }
        }
    }
}

impl<'a> Display for VmirDisplay<'a, &'a ResourceBody> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;
        write!(f, "{}", self.with((0usize, 0usize, &self.item.insts[..])))?;
        writeln!(f, "  result: ({}, {})", self.item.res.0, self.item.res.1)?;
        write!(f, "}}")
    }
}
