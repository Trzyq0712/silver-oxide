use crate::vmir::Type;
use crate::vmir::display::VmirDisplay;
use std::fmt::{self, Display, Formatter};

/// A heap-location member: `location f(params): ret bound`. Applying it yields an
/// address (`Addr<ret>`), the *only* way a heap address is produced. `ret` is the
/// held value type. The `bound` caps the total permission a single cell may hold
/// (fields: `Bounded(1/1)`; predicates: `Unbounded`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Location {
    pub params: Vec<Type>,
    pub ret: Type,
    pub bound: Bound,
}

/// Permission bound of a [`Location`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Bound {
    /// At most this much total permission per cell (a real literal).
    Bounded(num::BigRational),
    /// No bound (predicates).
    Unbounded,
}

impl<'a> Display for VmirDisplay<'a, &'a Location> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, param) in self.item.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "e{i}: {}", self.with(param))?;
        }
        write!(f, "): {} ", self.with(&self.item.ret))?;
        match &self.item.bound {
            // Match the permission-literal rendering (`1/1`, never reduced).
            Bound::Bounded(p) => write!(f, "bound {}/{}", p.numer(), p.denom()),
            Bound::Unbounded => write!(f, "unbounded"),
        }
    }
}
