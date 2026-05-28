use crate::impl_pure_inst_display;
use crate::vmir::display::VmirDisplay;
use crate::vmir::heap::write_heap_inst_with;
use crate::vmir::inst::{Bumps, write_inst_block};
use crate::vmir::{HeapInst, HeapVal, Inst, InstContext, PathConds, ResourceCall, Val};
use std::fmt::{self, Display, Formatter};

pub struct MethodCtx;

impl InstContext for MethodCtx {
    type InstExt = InstExt;
    type HeapExt = HeapExt;
    type PureExt = PureExt;
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

impl<'a> Display for VmirDisplay<'a, (usize, usize, &'a PathConds, &'a InstExt)> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let (e_idx, h_idx, pc, ext) = self.item;
        match ext {
            InstExt::Assume(v) => writeln!(f, "  {pc} assume {v}"),
            InstExt::Assert(v) => writeln!(f, "  {pc} assert {v}"),
            InstExt::ResourceCall(call) => {
                write!(
                    f,
                    "  (h{h_idx}, e{e_idx}) := {pc} call {}[{}](",
                    self.interner.resolve(&call.resource),
                    call.ctx_heap,
                )?;
                for (i, arg) in call.args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                writeln!(f, ")")
            }
        }
    }
}

impl Display for HeapExt {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            HeapExt::Assign(heap, Assign { loc, val }) => {
                write!(f, "assign[{heap}] {loc} := {val}")
            }
        }
    }
}

/// `Display for HeapInst<HeapExt>` — delegates the shared variants to the
/// helper and renders `Ext` via the `Display for HeapExt` impl.
impl Display for HeapInst<HeapExt> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write_heap_inst_with(self, f)
    }
}

impl<'a> Display for VmirDisplay<'a, &'a PureExt> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            PureExt::Perm(heap, loc) => write!(f, "perm[{heap}] {loc}"),
        }
    }
}

impl_pure_inst_display!(PureExt);

impl<'a> Display for VmirDisplay<'a, &'a Method> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;
        write_inst_block(f, self, &self.item.insts, 0, 0)?;
        write!(f, "}}")
    }
}
