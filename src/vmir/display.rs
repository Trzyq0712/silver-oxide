//! Display infrastructure for VMIR: the interner-aware `VmirDisplay`
//! wrapper plus the top-level `Program` / `Declaration` Display impls.
//!
//! Per-type `Display` impls live next to their types; the inst-block
//! walker lives in `vmir/inst.rs`.

use crate::vmir::{Declaration, MemberId, Program, Snapshot};
use lasso::Rodeo;
use std::fmt::{self, Display, Formatter, Write};

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

impl Program {
    /// Render the resources' *derived* members — the address location and
    /// snapshot that plain VMIR does not store (`Resource::derive_location` /
    /// `derive_snapshot`). For `--derived` debug dumps.
    pub fn derived_dump(&self) -> String {
        let mut out = String::new();
        for (id, decl) in self.decls.iter_enumerated() {
            let Declaration::Resource(r) = decl else {
                continue;
            };
            let name = self.interner.resolve(&id);
            // The derived address location (kind `location`, like a real decl).
            let loc = r.derive_location(id);
            let _ = writeln!(
                out,
                "location {name}@addr{}",
                VmirDisplay::new(&loc, &self.interner)
            );
            // The derived snapshot type, printed by kind for every snapshottable
            // (self-framed) resource: a concrete one is an `adt` with a single
            // constructor; an abstract one is an opaque empty `domain`.
            match r.derive_snapshot() {
                Some(Snapshot::Concrete(adt)) => {
                    let _ = writeln!(
                        out,
                        "adt {name}@snap {}",
                        VmirDisplay::new(&adt, &self.interner)
                    );
                }
                Some(Snapshot::Abstract(domain)) => {
                    let _ = writeln!(
                        out,
                        "domain {name}@snap {}",
                        VmirDisplay::new(&domain, &self.interner)
                    );
                }
                None => {}
            }
        }
        out
    }
}

impl Display for Program {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for item in self.decls.iter_enumerated() {
            // No `@addr`/`@snap` decls are emitted anymore — a predicate's address
            // location and snapshot are derived (`Resource::derive_location` /
            // `derive_snapshot`); fields are bare-named. So nothing to hide here.
            if !first {
                writeln!(f)?;
            }
            first = false;
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
            Declaration::Function(function) => write!(f, "function {name}{}", self.with(function)),
            Declaration::Location(location) => write!(f, "location {name}{}", self.with(location)),
            Declaration::Method(method) => write!(f, "method {name} {}", self.with(method)),
            Declaration::Resource(resource) => write!(f, "resource {name}{}", self.with(resource)),
            Declaration::Adt(adt) => write!(f, "adt {name} {}", self.with(adt)),
        }
    }
}
