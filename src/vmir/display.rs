use crate::vmir::{
    Acc, Adt, Assign, BinOp, Declaration, Domain, Function, FunctionCall, HeapExt, HeapInst,
    HeapVal, Inst, InstContext, InstExt, InstKind, Literal, MemberId, Method, PathConds, Polarity,
    Program, PureInst, Resource, ResourceBody, ResourcePureExt, Type, Val,
};
use lasso::Rodeo;
use std::fmt::{self, Display, Formatter};

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

/// Rendering hook for the `PureInst::Ext` payload.
pub(crate) trait PureExtRender {
    fn render(&self, f: &mut Formatter<'_>) -> fmt::Result;
}

impl PureExtRender for ! {
    fn render(&self, _: &mut Formatter<'_>) -> fmt::Result {
        match *self {}
    }
}

impl PureExtRender for ResourcePureExt {
    fn render(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ResourcePureExt::CtxDeref(addr) => write!(f, "*[ctx] {addr}"),
        }
    }
}

/// Rendering hook for the `HeapInst::Ext` payload. Implementors are
/// responsible for emitting the right-hand-side of `h{i} := <pc> ...`.
pub(crate) trait HeapExtRender {
    fn render(&self, f: &mut Formatter<'_>) -> fmt::Result;
}

impl HeapExtRender for ! {
    fn render(&self, _: &mut Formatter<'_>) -> fmt::Result {
        match *self {}
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

/// Rendering hook for the `InstKind::Ext` payload. Implementors mutate the
/// running val/heap counters per-variant (e.g. `ResourceCall` bumps both).
pub(crate) trait InstExtRender {
    fn render(
        &self,
        f: &mut Formatter<'_>,
        pc: &PathConds,
        val_idx: &mut usize,
        heap_idx: &mut usize,
        interner: &Rodeo<MemberId>,
    ) -> fmt::Result;
}

impl InstExtRender for ! {
    fn render(
        &self,
        _: &mut Formatter<'_>,
        _: &PathConds,
        _: &mut usize,
        _: &mut usize,
        _: &Rodeo<MemberId>,
    ) -> fmt::Result {
        match *self {}
    }
}

impl InstExtRender for InstExt {
    fn render(
        &self,
        f: &mut Formatter<'_>,
        pc: &PathConds,
        val_idx: &mut usize,
        heap_idx: &mut usize,
        interner: &Rodeo<MemberId>,
    ) -> fmt::Result {
        match self {
            InstExt::Assume(v) => writeln!(f, "  {pc} assume {v}"),
            InstExt::Assert(v) => writeln!(f, "  {pc} assert {v}"),
            InstExt::ResourceCall(call) => {
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

fn write_inst_block<'a, T, C: InstContext>(
    f: &mut Formatter<'_>,
    ctx: &VmirDisplay<'a, T>,
    insts: &[Inst<C>],
    val_base: usize,
) -> fmt::Result
where
    C::InstExt: InstExtRender,
    C::PureExt: PureExtRender,
    C::HeapExt: HeapExtRender,
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

fn write_heap_inst<H: HeapExtRender>(f: &mut Formatter<'_>, inst: &HeapInst<H>) -> fmt::Result {
    match inst {
        HeapInst::Acc(Acc { loc, perm }) => write!(f, "acc({loc}, {perm})"),
        HeapInst::Add(lhs, rhs) => write!(f, "{lhs} + {rhs}"),
        HeapInst::Sub(lhs, rhs) => write!(f, "{lhs} - {rhs}"),
        HeapInst::Ternary(cond, lhs, rhs) => write!(f, "{cond} ? {lhs} : {rhs}"),
        HeapInst::Ext(ext) => ext.render(f),
    }
}

impl Display for PathConds {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "<")?;
        for (i, (val, pol)) in self.lits.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            if matches!(pol, Polarity::Negative) {
                write!(f, "!")?;
            }
            write!(f, "{val}")?;
        }
        write!(f, ">")
    }
}

impl<'a, P> Display for VmirDisplay<'a, &'a PureInst<P>>
where
    P: PureExtRender,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            PureInst::Fresh => write!(f, "fresh"),
            PureInst::Binary(op, lhs, rhs) => write!(f, "{lhs} {op} {rhs}"),
            PureInst::Ternary(cond, then_val, else_val) => {
                write!(f, "{cond} ? {then_val} : {else_val}")
            }
            PureInst::Deref(heap, loc) => write!(f, "*[{heap}] {loc}"),
            PureInst::Perm(heap, loc) => write!(f, "perm[{heap}] {loc}"),
            PureInst::FunctionCall(call) => write!(f, "{}", self.with(call)),
            PureInst::Ext(ext) => ext.render(f),
        }
    }
}

impl<'a> Display for VmirDisplay<'a, &'a FunctionCall> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}[{}](",
            self.interner.resolve(&self.item.function),
            self.item.ctx_heap
        )?;
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

impl Display for HeapVal {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            HeapVal::Empty => write!(f, "empty"),
            HeapVal::Temp(i) => write!(f, "h{i}"),
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
