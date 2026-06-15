use crate::vmir::MemberId;
use crate::vmir::display::VmirDisplay;
use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Adt {}

/// ADT structure the verifier needs to drive constructor/discriminator
/// reductions. Built during translation (it spans the synthesized constructor
/// and `@tag` declarations) and carried on the `Program`.
#[derive(Debug, Clone, Default)]
pub struct AdtMeta {
    /// Per-ADT `@tag` function id → (constructor id → tag index). The tag
    /// reduction `Adt@tag(ctor_C(..)) ⇒ index_C` is generated from this.
    pub tag_fns: HashMap<MemberId, HashMap<MemberId, usize>>,
    /// Destructor accessor function id → `(constructor id, field index)`. The
    /// projection reduction `accessor(ctor_C(a0..an)) ⇒ a_index` is generated
    /// from this.
    pub dtors: HashMap<MemberId, (MemberId, usize)>,
}

impl<'a> Display for VmirDisplay<'a, &'a Adt> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let _ = self.item;
        write!(f, "{{}}")
    }
}
