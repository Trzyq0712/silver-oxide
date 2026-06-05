use crate::vmir::display::VmirDisplay;
use crate::vmir::{HeapVal, Inst, MemberId, Type, Val};
use std::fmt::{self, Display, Formatter};

/// A reusable unit of proof.
///
/// A resource computes a heap delta and a boolean condition.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Resource {
    pub params: Vec<Type>,
    pub requires: Option<(MemberId, Vec<Val>)>,
    pub body: Option<ResourceBody>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResourceBody {
    pub insts: Vec<Inst>,
    pub res: (crate::vmir::HeapVal, Val),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResourceCall {
    pub resource: MemberId,
    pub ctx_heap: HeapVal,
    pub args: Vec<Val>,
}

// ======================
// DISPLAY INFRASTRUCTURE
// ======================

impl<'a> Display for VmirDisplay<'a, &'a Resource> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, param) in self.item.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", self.with(param))?;
        }
        write!(f, ")")?;

        match &self.item.body {
            None => Ok(()),
            Some(body) => {
                write!(f, "[")?;
                match &self.item.requires {
                    None => write!(f, "empty")?,
                    Some((req_id, req_args)) => {
                        write!(f, "{}(", self.interner.resolve(req_id))?;
                        for (i, arg) in req_args.iter().enumerate() {
                            if i > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{}", arg)?;
                        }
                        write!(f, ")")?;
                    }
                }
                writeln!(f, "] {{")?;
                write!(
                    f,
                    "{}",
                    self.with((self.item.params.len(), 1usize, &body.insts[..]))
                )?;
                writeln!(f, "  result: ({}, {})", body.res.0, body.res.1)?;
                write!(f, "}}")
            }
        }
    }
}

impl<'a> Display for VmirDisplay<'a, &'a ResourceBody> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;
        write!(f, "{}", self.with((0usize, 0usize, &self.item.insts[..])))?;
        writeln!(f, "  result: ({}, {})", self.item.res.0, self.item.res.1)?;
        write!(f, "}}")
    }
}
