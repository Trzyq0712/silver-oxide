use crate::vmir;
use crate::vmir::ast::*;
use crate::vmir::heap_exp;
use crate::vmir::method as method_ir;
use crate::vmir::method::HeapAssign;
use crate::vmir::HeapDepInstKind;
use crate::vmir::Type;
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
        for item in self.decls.iter_enumerated() {
            let display = VmirDisplay::new(item, &self.interner);
            writeln!(f, "{display}")?;
            writeln!(f)?;
        }
        Ok(())
    }
}

impl<'a> Display for VmirDisplay<'a, (MemberId, &'a Declaration)> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let (id, decl) = self.item;
        match decl {
            Declaration::Domain(_) => write!(f, "domain {}", self.interner.resolve(&id)),
            Declaration::DomainElement => write!(f, "// DomainElement"),
            Declaration::Function(func) => write!(f, "{}", self.with(func)),
            Declaration::Method(method) => write!(f, "{}", self.with(method)),
            Declaration::Resource(resource) => write!(f, "{}", self.with(resource)),
            Declaration::Adt(adt) => write!(f, "adt {}", self.interner.resolve(&adt.name)),
            Declaration::AdtConstructor => write!(f, "// AdtConstructor"),
            Declaration::HeapExp(exp) => {
                writeln!(f, "heap_exp {}", self.interner.resolve(&id))?;
                write!(f, "{}", self.with(exp))
            }
        }
    }
}

impl<'a> Display for VmirDisplay<'a, &'a Function> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "function {}(", self.interner.resolve(&self.item.name))?;
        for (i, arg) in self.item.signature.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", self.with(arg))?;
        }
        write!(f, "): {}", self.with(&self.item.signature.ret))?;

        if self.item.body.is_some() {
            writeln!(f, " {{")?;
            writeln!(f, "  // body")?;
            write!(f, "}}")?;
        }

        Ok(())
    }
}

impl<'a> Display for VmirDisplay<'a, &'a Method> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "method {}(", self.interner.resolve(&self.item.name))?;
        for (i, arg) in self.item.signature.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", self.with(arg))?;
        }
        write!(f, ")")?;

        if !self.item.signature.rets.is_empty() {
            write!(f, " returns (")?;
            for (i, ret) in self.item.signature.rets.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", self.with(ret))?;
            }
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl<'a> Display for VmirDisplay<'a, &'a Resource> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "resource {}(", self.interner.resolve(&self.item.name))?;
        for (i, arg) in self.item.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", self.with(arg))?;
        }
        write!(f, "): &{}", self.interner.resolve(&self.item.snapshot))?;

        if let Some(body) = &self.item.body {
            writeln!(f, " {{")?;
            write!(f, "{}", self.with(body))?;
            write!(f, "}}")?;
        }

        Ok(())
    }
}

impl<'a> Display for VmirDisplay<'a, &'a heap_exp::HeapExp> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, ty) in self.item.input_types.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "e{i}: {}", self.with(ty))?;
        }
        writeln!(f, "]")?;

        for (idx, heap_exp::HeapInst { kind, ty }) in self.item.insts.iter().enumerate() {
            writeln!(
                f,
                "e{}: {} := {}",
                idx + self.item.input_types.len(),
                self.with(ty),
                self.with(kind)
            )?;
        }

        writeln!(f, "({}, {})", self.item.res_impure, self.item.res_pure)
    }
}

impl<'a> Display for VmirDisplay<'a, &'a heap_exp::HeapInstKind> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            heap_exp::HeapInstKind::Pure(inst) => write!(f, "{}", self.with(inst)),
            heap_exp::HeapInstKind::Acc(acc) => write!(f, "{acc}"),
        }
    }
}

impl<'a> Display for VmirDisplay<'a, &'a method_ir::Method> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for (idx, method_ir::Inst { kind, ty }) in self.item.0.iter().enumerate() {
            writeln!(f, "e{idx}: {} := {}", self.with(ty), self.with(kind))?;
        }
        Ok(())
    }
}

impl<'a> Display for VmirDisplay<'a, &'a method_ir::InstKind> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            method_ir::InstKind::Fresh => write!(f, "fresh"),
            method_ir::InstKind::Pure(inst) => write!(f, "{}", self.with(inst)),
            method_ir::InstKind::HeapOp(op, member, args) => {
                write!(f, "{} {}(", op, self.interner.resolve(member))?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
            method_ir::InstKind::HeapAssign(HeapAssign { heap, addr, val }) => {
                write!(f, "*[{heap}]{addr} := {val}")
            }
        }
    }
}

impl<'a> Display for VmirDisplay<'a, &'a vmir::PureInst> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            vmir::PureInst::Unary(op, val) => write!(f, "{op}{val}"),
            vmir::PureInst::Binary(op, lhs, rhs) => write!(f, "{lhs} {op} {rhs}"),
            vmir::PureInst::Ternary(cond, then_val, else_val) => {
                write!(f, "{cond} ? {then_val} : {else_val}")
            }
            vmir::PureInst::Call(func_id, args) => {
                write!(f, "{}(", self.interner.resolve(func_id))?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
            vmir::PureInst::Heap(heap_inst) => match &heap_inst.kind {
                HeapDepInstKind::Perm(addr) => write!(f, "perm[{}] {addr}", heap_inst.heap),
                HeapDepInstKind::Deref(addr) => write!(f, "*[{}] {addr}", heap_inst.heap),
            },
        }
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
