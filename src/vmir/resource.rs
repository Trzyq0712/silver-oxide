use crate::vmir::display::VmirDisplay;
use crate::vmir::pure::PureExtRender;
use crate::vmir::{HeapVal, Inst, InstContext, MemberId, Type, Val};
use lasso::Rodeo;
use std::fmt::{self, Display, Formatter};

pub struct ResourceCtx;

impl InstContext for ResourceCtx {
    type PureExt = ResourcePureExt;
}

/// Pure-instruction extensions only legal in resource bodies.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ResourcePureExt {
    /// Dereference an address in the resource's context (precondition) heap.
    /// SIDECOND: the context heap must have positive permission amount
    /// for this location.
    CtxDeref(Val),
    /// Call a function evaluated in the resource's context heap.
    CtxFunctionCall(crate::vmir::FunctionCall),
}

pub type ResourceInst = Inst<ResourceCtx>;

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
    pub insts: Vec<ResourceInst>,
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

impl PureExtRender for ResourcePureExt {
    fn render(&self, f: &mut Formatter<'_>, interner: &Rodeo<MemberId>) -> fmt::Result {
        match self {
            ResourcePureExt::CtxDeref(addr) => write!(f, "*[ctx] {addr}"),
            ResourcePureExt::CtxFunctionCall(call) => {
                write!(f, "{}[ctx](", interner.resolve(&call.function))?;
                for (i, arg) in call.args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
        }
    }
}

impl crate::vmir::inst::UsesPc for ResourcePureExt {
    fn uses_pc(&self) -> bool {
        match self {
            // Both have SIDECONDs (ctx-heap perm / function precondition).
            ResourcePureExt::CtxDeref(_) | ResourcePureExt::CtxFunctionCall(_) => true,
        }
    }
}

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

        if let Some((req_id, req_args)) = &self.item.requires {
            write!(f, " requires {}(", self.interner.resolve(req_id))?;
            for (i, arg) in req_args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", arg)?;
            }
            write!(f, ")")?;
        }

        match &self.item.body {
            None => Ok(()),
            Some(body) => {
                writeln!(f, " {{")?;
                write!(
                    f,
                    "{}",
                    self.with((self.item.params.len(), 0usize, &body.insts[..]))
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
