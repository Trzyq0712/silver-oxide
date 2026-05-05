use crate::vmir::{
    Adt, BinOp, Declaration, Domain, Function, HeapInst, HeapVal, Inst, MemberId, Method, Program,
    PureInst, Resource, Type, UnOp, Val,
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

        writeln!(f, " {{")?;
        let base = self.item.params.len();
        for (idx, inst) in self.item.insts.iter().enumerate() {
            writeln!(f, "  e{}: {}", idx + base, self.with(inst))?;
        }
        writeln!(f, "  result: ({}, {})", self.item.res.0, self.item.res.1)?;
        write!(f, "}}")
    }
}

impl<'a> Display for VmirDisplay<'a, &'a Method> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;
        for (idx, inst) in self.item.insts.iter().enumerate() {
            writeln!(f, "  e{idx}: {}", self.with(inst))?;
        }
        write!(f, "}}")
    }
}

impl<'a> Display for VmirDisplay<'a, &'a Inst> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            Inst::Assume(cond) => write!(f, "assume {cond}"),
            Inst::Assert(cond) => write!(f, "assert {cond}"),
            Inst::ResourceCall(_) => write!(f, "resource_call(/* opaque */)"),
            Inst::Heap(inst) => write!(f, "{inst}"),
            Inst::Pure(ty, inst) => write!(f, "{} := {}", self.with(ty), self.with(inst)),
        }
    }
}

impl<'a> Display for VmirDisplay<'a, &'a PureInst> {
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
            PureInst::HeapSubset(lhs, rhs) => write!(f, "{lhs} ⊑ {rhs}"),
        }
    }
}

impl<'a> Display for VmirDisplay<'a, &'a FunctionCall> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}[{}](",
            self.interner.resolve(&self.item.func_id),
            self.item.heap_ctx
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
            HeapVal::Implicit => write!(f, "_"),
            HeapVal::Temp(i) => write!(f, "h{i}"),
        }
    }
}

impl Display for HeapInst {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            HeapInst::Acc(acc) => write!(f, "acc({}, {})", acc.loc, acc.perm),
            HeapInst::Add(lhs, rhs) => write!(f, "{lhs} + {rhs}"),
            HeapInst::Sub(lhs, rhs) => write!(f, "{lhs} - {rhs}"),
            HeapInst::Ternary(cond, lhs, rhs) => write!(f, "{cond} ? {lhs} : {rhs}"),
            HeapInst::Assign(heap, val) => write!(f, "{heap} := {val}"),
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
