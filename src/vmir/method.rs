use crate::vmir::display::VmirDisplay;
use crate::vmir::heap::HeapExtRender;
use crate::vmir::inst::{Bumps, PcPrefix};
use crate::vmir::pure::PureExtRender;
use crate::vmir::{HeapVal, Inst, InstContext, MemberId, PathConds, ResourceCall, Val};
use lasso::Rodeo;
use std::fmt::{self, Display, Formatter};

pub struct MethodCtx;

impl InstContext for MethodCtx {
    type InstExt = InstExt;
    type HeapExt = HeapExt;
    type PureExt = PureExt;

    fn perm_pure_ext(heap: HeapVal, loc: Val) -> Option<Self::PureExt> {
        Some(PureExt::Perm(heap, loc))
    }
}

/// Method-specific instruction extensions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InstExt {
    Assume(Val),
    Assert(Val),
    ResourceCall(ResourceCall),
}

/// Method-specific heap-instruction extensions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HeapExt {
    /// Assign a value to a heap location in a given heap.
    /// SIDECOND: The heap location must have at least `write` amount of
    /// permission.
    Assign(HeapVal, Assign),
}

/// Method-specific pure-instruction extensions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PureExt {
    /// Query the permission amount of an address in a heap.
    Perm(HeapVal, Val),
}

/// Assign a value to a heap location.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Assign {
    pub loc: Val,
    pub val: Val,
}

/// Concrete `Inst` for method bodies.
pub type MethodInst = Inst<MethodCtx>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Method {
    pub insts: Vec<MethodInst>,
}

// ======================
// DISPLAY INFRASTRUCTURE
// ======================

impl Bumps for InstExt {
    fn bumps(&self) -> (usize, usize) {
        match self {
            InstExt::Assume(_) | InstExt::Assert(_) => (0, 0),
            // `ResourceCall` produces a `(heap_delta, bool)` pair.
            InstExt::ResourceCall(_) => (1, 1),
        }
    }
}

impl crate::vmir::inst::UsesPc for InstExt {
    fn uses_pc(&self) -> bool {
        match self {
            InstExt::Assume(_) | InstExt::Assert(_) | InstExt::ResourceCall(_) => true,
        }
    }
}

impl crate::vmir::inst::UsesPc for HeapExt {
    fn uses_pc(&self) -> bool {
        match self {
            HeapExt::Assign(..) => true,
        }
    }
}

impl crate::vmir::inst::UsesPc for PureExt {
    fn uses_pc(&self) -> bool {
        match self {
            PureExt::Perm(..) => false,
        }
    }
}

impl<'a> Display for VmirDisplay<'a, (usize, usize, &'a PathConds, &'a InstExt)> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let (e_idx, h_idx, pc, ext) = self.item;
        match ext {
            InstExt::Assume(v) => writeln!(f, "  {}assume {v}", PcPrefix(pc)),
            InstExt::Assert(v) => writeln!(f, "  {}assert {v}", PcPrefix(pc)),
            InstExt::ResourceCall(call) => {
                write!(
                    f,
                    "  (h{h_idx}, e{e_idx}) := {}call {}(",
                    PcPrefix(pc),
                    self.interner.resolve(&call.resource),
                )?;
                for (i, arg) in call.args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                writeln!(f, ")[{}]", call.ctx_heap)
            }
        }
    }
}

impl HeapExtRender for HeapExt {
    fn render(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            HeapExt::Assign(heap, Assign { loc, val }) => {
                write!(f, "assign[{heap}] {loc} := {val}")
            }
        }
    }
}

impl PureExtRender for PureExt {
    fn render(&self, f: &mut Formatter<'_>, _: &Rodeo<MemberId>) -> fmt::Result {
        match self {
            PureExt::Perm(heap, loc) => write!(f, "perm[{heap}] {loc}"),
        }
    }
}

impl<'a> Display for VmirDisplay<'a, &'a Method> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;
        write!(f, "{}", self.with((0usize, 0usize, &self.item.insts[..])))?;
        write!(f, "}}")
    }
}
