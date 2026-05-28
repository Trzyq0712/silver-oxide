use crate::vmir::display::VmirDisplay;
use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Adt {}

impl<'a> Display for VmirDisplay<'a, &'a Adt> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let _ = self.item;
        write!(f, "{{}}")
    }
}
