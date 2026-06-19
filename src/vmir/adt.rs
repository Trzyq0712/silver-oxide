use crate::vmir::MemberId;
use crate::vmir::display::VmirDisplay;
use std::fmt::{self, Display, Formatter};

/// An algebraic data type: its discriminator `@tag` function and its
/// constructors. The verifier derives its constructor/discriminator reduction
/// rules from this structure (see `verify::meta`); no separate side-table is
/// carried on the `Program`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Adt {
    /// The `@tag` discriminator function id (`Adt@tag(ctor_C(..)) ⇒ tag_C`).
    pub tag_fn: MemberId,
    pub constructors: Vec<AdtConstructor>,
}

/// One constructor of an [`Adt`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AdtConstructor {
    /// The constructor function id.
    pub ctor_fn: MemberId,
    /// The constructor's discriminator tag (its `@tag` value).
    pub tag: usize,
    /// The field destructor/accessor function ids, in field order: `projections[i]`
    /// projects field `i` (`projections[i](ctor_fn(a0..an)) ⇒ a_i`).
    pub projections: Vec<MemberId>,
}

impl<'a> Display for VmirDisplay<'a, &'a Adt> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let adt = self.item;
        write!(f, "{{ @tag = fn{}", usize::from(adt.tag_fn))?;
        for c in &adt.constructors {
            write!(f, ", fn{}#{}", usize::from(c.ctor_fn), c.tag)?;
        }
        write!(f, " }}")
    }
}
