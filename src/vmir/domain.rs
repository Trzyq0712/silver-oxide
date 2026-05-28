use crate::vmir::display::VmirDisplay;
use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Domain {}

impl<'a> Display for VmirDisplay<'a, &'a Domain> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let _ = self.item;
        write!(f, "{{}}")
    }
}
