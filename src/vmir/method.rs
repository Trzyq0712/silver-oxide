use crate::vmir::Inst;
use crate::vmir::display::VmirDisplay;
use lasso::Spur;
use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Method {
    pub name: Spur,
    pub insts: Vec<Inst>,
}

// ======================
// DISPLAY INFRASTRUCTURE
// ======================

impl<'a> Display for VmirDisplay<'a, &'a Method> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = self.interner.resolve(&self.item.name);
        writeln!(f, "method {name} {{")?;
        write!(f, "{}", self.with((0usize, 0usize, &self.item.insts[..])))?;
        write!(f, "}}")
    }
}
