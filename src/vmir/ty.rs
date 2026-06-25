use crate::vmir::MemberId;
use crate::vmir::display::VmirDisplay;
use lasso::{Key, Spur};
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
    /// `Option[T]` — a builtin parametric type (like `Seq[T]`/`Set[T]` later): a
    /// domain with axiomatized functions. The verifier resolves it to its `Option`
    /// ADT instance via the mono registry; it is never a user declaration.
    Option(Box<Type>),
    /// A heap address `&[group] value @ bound` — the type of a location. Self-
    /// describing: it carries the **held value type** `value`, the permission
    /// **bound** (`Bounded(1/1)` for fields, `Unbounded` for predicates), and a
    /// **grouping tag** `group` (an interned `Spur` in `Program.groups`, *not* a
    /// declaration) that distinguishes e.g. two `Int` fields and scopes
    /// non-aliasing. Because all of this lives in the type (not a side table keyed
    /// by a syntactic node), addresses can be **computed over** and still recover
    /// their metadata.
    Addr {
        group: Spur,
        value: Box<Type>,
        bound: Bound,
    },
    /// A type parameter of the enclosing generic declaration, by 0-based index
    /// (e.g. `Generic(0)` is the `Some` field type of the generic `Option` ADT).
    /// Substituted by the type arguments at monomorphization.
    Generic(usize),
}

/// Permission bound of a heap location (cap on total permission per cell).
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Bound {
    /// At most this much total permission per cell (a real literal).
    Bounded(num::BigRational),
    /// No bound (predicates).
    Unbounded,
}

impl Type {
    /// A domain/ADT type with no type arguments.
    pub fn domain(id: MemberId) -> Self {
        Type::Domain(id, Box::new([]))
    }

    /// An address type holding `value`, grouped under `group`, capped at `bound`.
    pub fn addr(group: Spur, value: Type, bound: Bound) -> Self {
        Type::Addr {
            group,
            value: Box::new(value),
            bound,
        }
    }

    /// The inner `T` of an `Option[T]`, or `None` for any other type.
    pub fn option_inner(&self) -> Option<&Type> {
        match self {
            Type::Option(inner) => Some(inner),
            _ => None,
        }
    }

    /// The held value type `T` of an address `&[g] T @ b`, else `None`.
    pub fn addr_value(&self) -> Option<&Type> {
        match self {
            Type::Addr { value, .. } => Some(value),
            _ => None,
        }
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
            Type::Option(ty) => write!(f, "Option[{ty}]"),
            Type::Addr {
                group,
                value,
                bound,
            } => write!(f, "&[g{}] {value} @ {bound}", group.into_usize()),
            Type::Generic(i) => write!(f, "?{i}"),
        }
    }
}

impl Display for Bound {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            // Match the permission-literal rendering (`1/1`, never reduced).
            Bound::Bounded(p) => write!(f, "{}/{}", p.numer(), p.denom()),
            Bound::Unbounded => write!(f, "*"),
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
            Type::Option(ty) => write!(f, "Option[{}]", self.with(ty.as_ref())),
            Type::Addr {
                group,
                value,
                bound,
            } => write!(
                f,
                "&[{}] {} @ {bound}",
                self.groups.resolve(group),
                self.with(value.as_ref())
            ),
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
