use crate::vmir::{
    Adt, BinOp, Declaration, Domain, Function, HeapInst, HeapVal, Inst, InstKind, Lit, MemberId,
    Method, MethodHeapExt, MethodInstExt, PathCond, Program, PureInst, Resource, ResourceBody,
    Type, UnOp, Val,
};
use lasso::Rodeo;
use std::fmt::{self, Display, Formatter};

use super::pure::{FunctionCall, Literal};

/// Helper wrapper for interner-aware VMIR formatting.
pub struct VmirDisplay<'a, T> {
    item: T,
    interner: &'a Rodeo<MemberId>,
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

impl<'a> Display for VmirDisplay<'a, &'a Domain> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let _ = self.item;
        write!(f, "{{}}")
    }
}

impl<'a> Display for VmirDisplay<'a, &'a Adt> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let _ = self.item;
        write!(f, "{{}}")
    }
}

impl<'a> Display for VmirDisplay<'a, &'a Function> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, param) in self.item.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", self.with(param))?;
        }
        write!(f, ") -> {}", self.with(&self.item.ret))
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
                write_inst_block(f, self, &body.insts, self.item.params.len())?;
                writeln!(f, "  result: ({}, {})", body.res.0, body.res.1)?;
                write!(f, "}}")
            }
        }
    }
}

impl<'a> Display for VmirDisplay<'a, &'a ResourceBody> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;
        write_inst_block(f, self, &self.item.insts, 0)?;
        writeln!(f, "  result: ({}, {})", self.item.res.0, self.item.res.1)?;
        write!(f, "}}")
    }
}

impl<'a> Display for VmirDisplay<'a, &'a Method> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;
        write_inst_block(f, self, &self.item.insts, 0)?;
        write!(f, "}}")
    }
}

/// Rendering hook for the `HeapVal::CtxHeap` payload. `()` (resource ctx)
/// prints `ctx`; `!` (method ctx) is uninhabited.
pub(crate) trait CtxHeapRender {
    fn render(&self, f: &mut Formatter<'_>) -> fmt::Result;
}

impl CtxHeapRender for () {
    fn render(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "ctx")
    }
}

impl CtxHeapRender for ! {
    fn render(&self, _: &mut Formatter<'_>) -> fmt::Result {
        match *self {}
    }
}

/// Rendering hook for the `HeapInst::Ext` payload. `MethodHeapExt` renders
/// like a heap inst (bumps the heap counter); `!` is uninhabited.
pub(crate) trait HeapExtRender {
    fn render(&self, f: &mut Formatter<'_>) -> fmt::Result;
}

impl HeapExtRender for ! {
    fn render(&self, _: &mut Formatter<'_>) -> fmt::Result {
        match *self {}
    }
}

impl HeapExtRender for MethodHeapExt {
    fn render(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            MethodHeapExt::Sub(l, r) => write!(f, "{l} - {r}"),
        }
    }
}

/// Rendering hook for the `InstKind::Ext` payload. Implementors mutate the
/// running val/heap counters per-variant (e.g. `ResourceCall` bumps both).
pub(crate) trait InstExtRender {
    fn render(
        &self,
        f: &mut Formatter<'_>,
        pc: &PathCond,
        val_idx: &mut usize,
        heap_idx: &mut usize,
        interner: &Rodeo<MemberId>,
    ) -> fmt::Result;
}

impl InstExtRender for ! {
    fn render(
        &self,
        _: &mut Formatter<'_>,
        _: &PathCond,
        _: &mut usize,
        _: &mut usize,
        _: &Rodeo<MemberId>,
    ) -> fmt::Result {
        match *self {}
    }
}

impl InstExtRender for MethodInstExt {
    fn render(
        &self,
        f: &mut Formatter<'_>,
        pc: &PathCond,
        val_idx: &mut usize,
        heap_idx: &mut usize,
        interner: &Rodeo<MemberId>,
    ) -> fmt::Result {
        match self {
            MethodInstExt::Assume(v) => writeln!(f, "  {pc} assume {v}"),
            MethodInstExt::Assert(v) => writeln!(f, "  {pc} assert {v}"),
            MethodInstExt::ResourceCall(call) => {
                write!(
                    f,
                    "  (h{heap_idx}, e{val_idx}) := {pc} call {}(",
                    interner.resolve(&call.resource)
                )?;
                for (i, arg) in call.args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                writeln!(f, ")")?;
                *heap_idx += 1;
                *val_idx += 1;
                Ok(())
            }
        }
    }
}

fn write_inst_block<'a, T, H, K, X>(
    f: &mut Formatter<'_>,
    ctx: &VmirDisplay<'a, T>,
    insts: &[Inst<H, K, X>],
    val_base: usize,
) -> fmt::Result
where
    H: HeapExtRender,
    K: InstExtRender,
    X: CtxHeapRender,
{
    let mut e_idx = val_base;
    let mut h_idx = 0usize;
    for inst in insts {
        match &inst.kind {
            InstKind::Pure(ty, pi) => {
                writeln!(
                    f,
                    "  e{e_idx}: {} := {} {}",
                    ctx.with(ty),
                    inst.pc,
                    ctx.with(pi)
                )?;
                e_idx += 1;
            }
            InstKind::Heap(hi) => {
                write!(f, "  h{h_idx} := {} ", inst.pc)?;
                write_heap_inst(f, hi)?;
                writeln!(f)?;
                h_idx += 1;
            }
            InstKind::Ext(ext) => {
                ext.render(f, &inst.pc, &mut e_idx, &mut h_idx, ctx.interner)?;
            }
        }
    }
    Ok(())
}

fn write_heap_inst<H, X>(f: &mut Formatter<'_>, inst: &HeapInst<H, X>) -> fmt::Result
where
    H: HeapExtRender,
    X: CtxHeapRender,
{
    match inst {
        HeapInst::Acc(acc) => write!(f, "acc({}, {})", acc.loc, acc.perm),
        HeapInst::Add(lhs, rhs) => write!(f, "{lhs} + {rhs}"),
        HeapInst::Ternary(cond, lhs, rhs) => write!(f, "{cond} ? {lhs} : {rhs}"),
        HeapInst::Ext(ext) => ext.render(f),
    }
}

impl Display for PathCond {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "<")?;
        for (i, lit) in self.lits.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{lit}")?;
        }
        write!(f, ">")
    }
}

impl Display for Lit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if !self.polarity {
            write!(f, "!")?;
        }
        write!(f, "{}", self.val)
    }
}

impl<'a, X> Display for VmirDisplay<'a, &'a PureInst<X>>
where
    X: CtxHeapRender,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            PureInst::Fresh => write!(f, "fresh"),
            PureInst::Unary(op, arg) => write!(f, "{op}{arg}"),
            PureInst::Binary(op, lhs, rhs) => write!(f, "{lhs} {op} {rhs}"),
            PureInst::Ternary(cond, then_val, else_val) => {
                write!(f, "{cond} ? {then_val} : {else_val}")
            }
            PureInst::Deref(heap, loc) => write!(f, "*[{heap}] {loc}"),
            PureInst::Perm(heap, loc) => write!(f, "perm[{heap}] {loc}"),
            PureInst::FunctionCall(call) => write!(f, "{}", self.with(call)),
        }
    }
}

impl<'a, X> Display for VmirDisplay<'a, &'a FunctionCall<X>>
where
    X: CtxHeapRender,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.interner.resolve(&self.item.func_id))?;
        if let Some(heap) = &self.item.heap_ctx {
            write!(f, "[{heap}]")?;
        }
        write!(f, "(")?;
        for (i, arg) in self.item.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{arg}")?;
        }
        write!(f, ")")
    }
}

impl<'a> Display for VmirDisplay<'a, &'a Type> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            Type::Domain(id) => write!(f, "{}", self.interner.resolve(id)),
            Type::Addr(ty) => write!(f, "&{}", self.with(ty.as_ref())),
            ty => write!(f, "{ty}"),
        }
    }
}

impl Display for Val {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Val::Literal(lit) => write!(f, "{lit}"),
            Val::Temp(i) => write!(f, "e{i}"),
        }
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Null => write!(f, "null"),
            Literal::Bool(b) => write!(f, "{b}"),
            Literal::Int(v) => write!(f, "{v}"),
            Literal::Real(v) => write!(f, "{v}"),
        }
    }
}

impl<X: CtxHeapRender> Display for HeapVal<X> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            HeapVal::Empty => write!(f, "empty"),
            HeapVal::Temp(i) => write!(f, "h{i}"),
            HeapVal::CtxHeap(x) => x.render(f),
        }
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let op = match self {
            BinOp::Plus => "+",
            BinOp::Minus => "-",
            BinOp::Mult => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::Eq => "==",
            BinOp::Lt => "<",
        };
        write!(f, "{op}")
    }
}

impl Display for UnOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let op = match self {
            UnOp::Not => "!",
            UnOp::Neg => "-",
        };
        write!(f, "{op}")
    }
}
