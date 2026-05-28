//! Display infrastructure for VMIR: the interner-aware `VmirDisplay`
//! wrapper plus the top-level `Program` / `Declaration` Display impls.
//!
//! Per-type `Display` impls live next to their types; the inst-block
//! walker lives in `vmir/inst.rs`.

use crate::vmir::{Declaration, MemberId, Program};
use lasso::Rodeo;
use std::fmt::{self, Display, Formatter};

/// Helper wrapper for interner-aware VMIR formatting. Fields are
/// `pub(super)` so sibling modules can implement `Display` impls on
/// `VmirDisplay<&MyType>`.
pub struct VmirDisplay<'a, T> {
    pub(super) item: T,
    pub(super) interner: &'a Rodeo<MemberId>,
}

impl<'a, T> VmirDisplay<'a, T> {
    pub fn new(item: T, interner: &'a Rodeo<MemberId>) -> Self {
        Self { item, interner }
    }

    pub fn with<U>(&self, item: U) -> VmirDisplay<'a, U> {
        VmirDisplay {
            item,
            interner: self.interner,
        }
    }
}

impl Display for Program {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for (idx, item) in self.decls.iter_enumerated().enumerate() {
            if idx > 0 {
                writeln!(f)?;
            }
            write!(f, "{}", VmirDisplay::new(item, &self.interner))?;
        }
        Ok(())
    }
}

impl<'a> Display for VmirDisplay<'a, (MemberId, &'a Declaration)> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let (id, decl) = self.item;
        let name = self.interner.resolve(&id);
        match decl {
            Declaration::Domain(domain) => write!(f, "domain {name} {}", self.with(domain)),
            Declaration::DomainElement => write!(f, "domain_element {name}"),
            Declaration::Function(function) => write!(f, "function {name}{}", self.with(function)),
            Declaration::Method(method) => write!(f, "method {name} {}", self.with(method)),
            Declaration::Resource(resource) => write!(f, "resource {name}{}", self.with(resource)),
            Declaration::Adt(adt) => write!(f, "adt {name} {}", self.with(adt)),
            Declaration::AdtConstructor => write!(f, "adt_constructor {name}"),
        }
    }
}
