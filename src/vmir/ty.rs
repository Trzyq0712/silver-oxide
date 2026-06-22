use crate::vmir::MemberId;
use crate::vmir::display::VmirDisplay;
use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Type {
    Int,
    Bool,
    Real,
    Ref,

    /// A domain/ADT type: the **generic** member id of the domain/ADT plus its
    /// type arguments. VMIR keeps types parametric (un-monomorphized); the
    /// verifier mints distinct monomorphic member ids per `(id, args)` instance.
    Domain(MemberId, Box<[Type]>),
    /// The snapshot type of a predicate, identified by the predicate's own
    /// Resource id (the snapshot ADT head). A single-variant ADT whose fields are
    /// the predicate's footprint slot types (`Resource.snapshot.field_types`);
    /// the verifier mints its constructor/projection ids on demand (see
    /// `verify::mono`). No `@snap` declaration is emitted — this is derived.
    Snap(MemberId),
    Addr(Box<Type>),
    /// A type parameter of the enclosing generic declaration, by 0-based index
    /// (e.g. `Generic(0)` is the `Some` field type of the generic `Option` ADT).
    /// Substituted by the type arguments at monomorphization.
    Generic(usize),
}

impl Type {
    /// A domain/ADT type with no type arguments.
    pub fn domain(id: MemberId) -> Self {
        Type::Domain(id, Box::new([]))
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Bool => write!(f, "Bool"),
            Type::Int => write!(f, "Int"),
            Type::Real => write!(f, "Real"),
            Type::Ref => write!(f, "Ref"),
            Type::Domain(id, args) => {
                write!(f, "d{}", id.0)?;
                fmt_args(f, args, |a, f| write!(f, "{a}"))
            }
            Type::Snap(id) => write!(f, "d{}@snap", id.0),
            Type::Addr(ty) => write!(f, "&{ty}"),
            Type::Generic(i) => write!(f, "?{i}"),
        }
    }
}

impl<'a> Display for VmirDisplay<'a, &'a Type> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            Type::Domain(id, args) => {
                write!(f, "{}", self.interner.resolve(id))?;
                fmt_args(f, args, |a, f| write!(f, "{}", self.with(a)))
            }
            Type::Snap(id) => write!(f, "{}@snap", self.interner.resolve(id)),
            Type::Addr(ty) => write!(f, "&{}", self.with(ty.as_ref())),
            ty => write!(f, "{ty}"),
        }
    }
}

/// Render `[a, b, …]` type arguments (nothing when empty).
fn fmt_args<T>(
    f: &mut Formatter<'_>,
    args: &[T],
    mut each: impl FnMut(&T, &mut Formatter<'_>) -> fmt::Result,
) -> fmt::Result {
    if args.is_empty() {
        return Ok(());
    }
    write!(f, "[")?;
    for (i, a) in args.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        each(a, f)?;
    }
    write!(f, "]")
}
