use crate::vmir::display::VmirDisplay;
use crate::vmir::{MemberId, Type};
use std::fmt::{self, Display, Formatter};

/// An algebraic data type: a list of variants (constructors), variant index =
/// discriminator tag. Purely semantic — no synthetic `@tag` / accessor member
/// ids. The verifier mints its own ids and reduction rules from this structure
/// (see `verify::mono`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Adt {
    pub variants: Vec<AdtVariant>,
}

/// One variant (constructor) of an [`Adt`]: an optional interned constructor
/// name (kept from the source; only needs to be distinct within the ADT — `None`
/// for synthetic ADTs like a predicate snapshot) plus its field types in order.
/// The constructor / projection / tag operations over it are the semantic
/// `PureInst::{AdtCons,AdtProj,AdtTag}` nodes; the verifier names its minted ids
/// `Adt::Ctor` (`@` is reserved for builtin suffixes, e.g. `Adt@tag`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AdtVariant {
    pub name: Option<MemberId>,
    pub field_types: Vec<Type>,
}

impl<'a> Display for VmirDisplay<'a, &'a Adt> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{ ")?;
        for (v, ctor) in self.item.variants.iter().enumerate() {
            if v > 0 {
                write!(f, " | ")?;
            }
            match ctor.name {
                Some(id) => write!(f, "{}(", self.interner.resolve(&id))?,
                None => write!(f, "_{v}(")?,
            }
            for (i, ty) in ctor.field_types.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", self.with(ty))?;
            }
            write!(f, ")")?;
        }
        write!(f, " }}")
    }
}
