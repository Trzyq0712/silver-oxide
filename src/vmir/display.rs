//! Display infrastructure for VMIR: the interner-aware `VmirDisplay`
//! wrapper plus the top-level `Program` / `Declaration` Display impls.
//!
//! Per-type `Display` impls live next to their types; the inst-block
//! walker lives in `vmir/inst.rs`.

use crate::vmir::{Declaration, MemberId, Program, Snapshot};
use lasso::{Rodeo, Spur};
use std::fmt::{self, Display, Formatter, Write};
use typed_index_collections::TiVec;

/// Helper wrapper for interner-aware VMIR formatting. Fields are
/// `pub(super)` so sibling modules can implement `Display` impls on
/// `VmirDisplay<&MyType>`.
pub struct VmirDisplay<'a, T> {
    pub(super) item: T,
    /// Program declarations, for resolving `MemberId` names.
    pub(super) decls: &'a TiVec<MemberId, Declaration>,
    /// Cheap string repr for member/constructor names.
    pub(super) interner: &'a Rodeo,
    /// Location-group tags (`Type::Addr.group`), for resolving group names.
    pub(super) groups: &'a Rodeo<Spur>,
}

impl<'a, T> VmirDisplay<'a, T> {
    pub fn new(
        item: T,
        decls: &'a TiVec<MemberId, Declaration>,
        interner: &'a Rodeo,
        groups: &'a Rodeo<Spur>,
    ) -> Self {
        Self {
            item,
            decls,
            interner,
            groups,
        }
    }

    pub fn with<U>(&self, item: U) -> VmirDisplay<'a, U> {
        VmirDisplay {
            item,
            decls: self.decls,
            interner: self.interner,
            groups: self.groups,
        }
    }

    /// The display name of a member id.
    pub(super) fn member(&self, id: MemberId) -> &'a str {
        self.interner.resolve(&self.decls[id].name())
    }

    /// The qualified constructor label of variant `variant` of ADT `adt`, e.g.
    /// `Nat::Succ` for a named constructor, or `Nat::#1` when the variant is
    /// anonymous (a synthetic snapshot variant). Mirrors the verifier's minted-id
    /// naming (`func_registry`).
    pub(super) fn adt_variant(&self, adt: MemberId, variant: usize) -> String {
        let base = self.member(adt);
        match &self.decls[adt] {
            Declaration::Adt(a) => match a.variants.get(variant).and_then(|v| v.name) {
                Some(name) => format!("{base}::{}", self.interner.resolve(&name)),
                None => format!("{base}::#{variant}"),
            },
            _ => format!("{base}::#{variant}"),
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
            let name = self.name(id);
            // The derived `@addr` accessor function (`params -> &[name] Snap @ *`).
            // Every predicate registers its group tag in `declare_predicate_accessors`.
            let group = self.groups.get(name).expect("predicate group tag");
            let loc = r.derive_location(id, group);
            let _ = writeln!(
                out,
                "function {name}@addr{}",
                VmirDisplay::new(&loc, &self.decls, &self.interner, &self.groups)
            );
            // The derived snapshot type, printed by kind for every snapshottable
            // (self-framed) resource: a concrete one is an `adt` with a single
            // constructor; an abstract one is an opaque empty `domain`.
            match r.derive_snapshot() {
                Some(Snapshot::Concrete(adt)) => {
                    let _ = writeln!(
                        out,
                        "adt {name}@snap {}",
                        VmirDisplay::new(&adt, &self.decls, &self.interner, &self.groups)
                    );
                }
                Some(Snapshot::Abstract(domain)) => {
                    let _ = writeln!(
                        out,
                        "domain {name}@snap {}",
                        VmirDisplay::new(&domain, &self.decls, &self.interner, &self.groups)
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
            // A field's address function is an ordinary `Declaration::Function`
            // (printed like any function); a predicate's address is its own
            // resource and its snapshot is derived (`Resource::derive_snapshot`).
            // No `@addr`/`@snap` member decls — nothing to hide here.
            if !first {
                writeln!(f)?;
            }
            first = false;
            write!(
                f,
                "{}",
                VmirDisplay::new(item.1, &self.decls, &self.interner, &self.groups)
            )?;
        }
        Ok(())
    }
}

impl<'a> Display for VmirDisplay<'a, &'a Declaration> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            Declaration::Domain(domain) => write!(f, "{}", self.with(domain)),
            Declaration::Axiom(ax) => write!(f, "{}", self.with(ax)),
            Declaration::Function(function) => write!(f, "{}", self.with(function)),
            Declaration::Method(method) => write!(f, "{}", self.with(method)),
            Declaration::Resource(resource) => write!(f, "{}", self.with(resource)),
            Declaration::Adt(adt) => write!(f, "{}", self.with(adt)),
        }
    }
}
