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

/// Per-resource ids the verifier needs for `fold`/`unfold`. (Predicates are a
/// Viper concept; in VMIR they are resources.) The snapshot is an ADT:
/// `snap_cons` packs the footprint field values, `snap_projs[i]` recovers slot
/// `i` (these are registered in [`AdtMeta::dtors`], so the projection reduction
/// makes fold→unfold round-trips exact).
#[derive(Debug, Clone)]
pub struct ResourceMeta {
    /// The resource's `@addr` function (its chunk address).
    pub addr_fn: MemberId,
    /// The snapshot constructor `P@snap@cons`.
    pub snap_cons: MemberId,
    /// The snapshot field accessors `P@snap@proj_i`, in footprint slot order.
    pub snap_projs: Vec<MemberId>,
}

impl<'a> Display for VmirDisplay<'a, &'a Adt> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let _ = self.item;
        write!(f, "{{}}")
    }
}
