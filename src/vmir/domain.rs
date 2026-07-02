use crate::vmir::display::VmirDisplay;
use crate::vmir::Inst;
use std::fmt::{self, Display, Formatter};

use lasso::Spur;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Domain {
    pub name: Spur,
    pub ty_params: TyParams,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DomainAxiom {
    pub name: Option<Spur>,
    pub ty_params: TyParams,
    pub body: Vec<Inst>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TyParams(usize);

impl From<usize> for TyParams {
    fn from(n: usize) -> Self {
        Self(n)
    }
}

impl Display for TyParams {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // A declaration's generic parameters are positional (`Generic(n)` → `?n`),
        // so the binder only states the **arity** (`<2>`); the params are referred
        // to as `?0`, `?1`, … Angle brackets match type-argument instantiation
        // (`[..]` is reserved for heaps / addr groups). Nothing is printed for a
        // non-generic declaration.
        if self.0 == 0 {
            return Ok(());
        }
        write!(f, "<{}>", self.0)
    }
}

impl<'a> Display for VmirDisplay<'a, &'a Domain> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = self.interner.resolve(&self.item.name);
        let ty_params = &self.item.ty_params;
        writeln!(f, "domain {name}{ty_params}")
    }
}

impl<'a> Display for VmirDisplay<'a, &'a DomainAxiom> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "axiom")?;
        if let Some(n) = &self.item.name {
            write!(f, " {}", self.interner.resolve(n))?;
        }
        writeln!(f, " {{")?;
        write!(f, "{}", self.with((0usize, 0usize, &self.item.body[..])))?;
        write!(f, "}}")
    }
}
