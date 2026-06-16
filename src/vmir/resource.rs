use crate::vmir::display::VmirDisplay;
use crate::vmir::{HeapVal, Inst, MemberId, Type, Val};
use std::fmt::{self, Display, Formatter};

/// A reusable unit of proof.
///
/// A resource computes a heap delta and a boolean condition.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Resource {
    pub params: Vec<Type>,
    pub precond: Precond,
    pub body: Option<ResourceBody>,
}

/// A resource's precondition mode.
///
/// - `SelfFramed`: one-state — the body reads only its own footprint. Predicates,
///   `@requires`, and function preconditions. Snapshottable / foldable.
/// - `Ctx(req, args)`: two-state — the body additionally reads a context heap
///   (`HeapVal::Temp(0)`), the delta of the precondition resource `req` applied
///   to `args` (the caller-supplied pre-state). `@ensures`. Opaque-only; never
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
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResourceBody {
    pub insts: Vec<Inst>,
    pub res: (crate::vmir::HeapVal, Val),
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
        write!(f, "(")?;
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
                write!(f, "[")?;
                match &self.item.precond {
                    Precond::SelfFramed => write!(f, "empty")?,
                    Precond::Ctx(req_id, req_args) => {
                        write!(f, "{}(", self.interner.resolve(req_id))?;
                        for (i, arg) in req_args.iter().enumerate() {
                            if i > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{}", arg)?;
                        }
                        write!(f, ")")?;
                    }
                }
                writeln!(f, "] {{")?;
                write!(
                    f,
                    "{}",
                    self.with((self.item.params.len(), 1usize, &body.insts[..]))
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
