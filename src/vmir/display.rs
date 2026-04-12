use crate::vmir::ast::*;
use crate::vmir::heap_exp;
use crate::vmir::method as method_ir;
use crate::vmir::Type;
use lasso::Rodeo;
use std::fmt::{self, Display, Formatter};

/// Helper struct for displaying VMIR with access to the string interner
pub struct VmirDisplay<'a, T> {
    item: &'a T,
    interner: &'a Rodeo<MemberId>,
    indent: usize,
}

impl<'a, T> VmirDisplay<'a, T> {
    pub fn new(item: &'a T, interner: &'a Rodeo<MemberId>) -> Self {
        Self {
            item,
            interner,
            indent: 0,
        }
    }

    pub fn with<U>(&self, item: &'a U) -> VmirDisplay<'a, U> {
        VmirDisplay {
            item,
            interner: self.interner,
            indent: self.indent,
        }
    }

    pub fn with_indent<U>(&self, item: &'a U) -> VmirDisplay<'a, U> {
        VmirDisplay {
            item,
            interner: self.interner,
            indent: self.indent + 1,
        }
    }

    /// Write the current indentation (2 spaces per level)
    fn write_indent(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for _ in 0..self.indent {
            write!(f, "  ")?;
        }
        Ok(())
    }
}

impl Display for Program {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for item in self.decls.iter_enumerated() {
            let display = VmirDisplay::new(&item, &self.interner);
            writeln!(f, "{}", display)?;
            writeln!(f)?; // Empty line between declarations
        }
        Ok(())
    }
}

impl<'a> Display for VmirDisplay<'a, (MemberId, &'a Declaration)> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let (id, decl) = self.item;
        match decl {
            Declaration::Domain(domain) => {
                let name = self.interner.resolve(id);
                write!(f, "domain {}", name)
            }
            Declaration::DomainElement => write!(f, "// DomainElement"),
            Declaration::Function(func) => {
                let display = self.with(func);
                write!(f, "{}", display)
            }
            Declaration::Method(method) => {
                let display = self.with(method);
                write!(f, "{}", display)
            }
            Declaration::Resource(resource) => {
                let display = self.with(resource);
                write!(f, "{}", display)
            }
            Declaration::Adt(adt) => {
                let name = self.interner.resolve(&adt.name);
                write!(f, "adt {}", name)
            }
            Declaration::AdtConstructor => write!(f, "// AdtConstructor"),
            Declaration::HeapExp(exp) => {
                let name = self.interner.resolve(id);
                writeln!(f, "heap_exp {name}")?;
                write!(f, "{}", self.with(exp))
            }
        }
    }
}

impl<'a> Display for VmirDisplay<'a, Function> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = self.interner.resolve(&self.item.name);

        self.write_indent(f)?;
        write!(f, "function {}", name)?;
        write!(f, "(")?;
        for (i, arg) in self.item.signature.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", self.with(arg))?;
        }
        write!(f, ")")?;

        write!(f, ": {}", self.with(&self.item.signature.ret))?;

        if let Some(ref _body) = self.item.body {
            writeln!(f, " {{")?;
            write!(f, "  // body")?;
            writeln!(f)?;
            write!(f, "}}")?;
        }

        Ok(())
    }
}

impl<'a> Display for VmirDisplay<'a, Method> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = self.interner.resolve(&self.item.name);

        self.write_indent(f)?;
        write!(f, "method {}", name)?;
        write!(f, "(")?;
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

        writeln!(f)?;
        // let contract_display = self.with_indent(&self.item.contract);
        // writeln!(f, "{}", contract_display)?;
        //
        // if let Some(ref body) = self.item.body {
        //     self.write_indent(f)?;
        //     writeln!(f, "{{")?;
        //     let body_display = self.with_indent(body);
        //     // write!(f, "{}", body_display)?;
        //     self.write_indent(f)?;
        //     writeln!(f, "}}")?;
        // }

        Ok(())
    }
}

impl<'a> Display for VmirDisplay<'a, MethContract> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let requires = &self.item.requires;
        self.write_indent(f)?;
        writeln!(f, "requires")?;
        write!(f, "{}", self.with_indent(requires))?;
        let ensures = &self.item.ensures;
        self.write_indent(f)?;
        writeln!(f, "ensures")?;
        write!(f, "{}", self.with_indent(ensures))?;
        Ok(())
    }
}

impl<'a> Display for VmirDisplay<'a, Resource> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = self.interner.resolve(&self.item.name);
        let snapshot_name = self.interner.resolve(&self.item.snapshot);

        self.write_indent(f)?;
        write!(f, "resource {}", name)?;
        write!(f, "(")?;
        for (i, arg) in self.item.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", self.with(arg))?;
        }
        write!(f, "): &{}", snapshot_name)?;

        if let Some(ref body) = self.item.body {
            writeln!(f, " {{")?;
            let exp_display = self.with_indent(body);
            write!(f, "{}", exp_display)?;
            self.write_indent(f)?;
            write!(f, "}}")?;
        }

        Ok(())
    }
}

impl<'a> Display for VmirDisplay<'a, heap_exp::HeapExp> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // Display input signatures
        self.write_indent(f)?;
        write!(f, "[")?;
        for (i, ty) in self.item.input_types.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "e{i}: {}", self.with(ty))?;
        }
        writeln!(f, "]")?;

        // Display the SSA instructions
        for (idx, heap_exp::Inst { kind, ty }) in self.item.insts.iter().enumerate() {
            self.write_indent(f)?;
            writeln!(
                f,
                "e{}: {} := {}",
                idx + self.item.input_types.len(),
                self.with(ty),
                self.with(kind)
            )?;
        }

        // Display the result
        self.write_indent(f)?;
        writeln!(
            f,
            "({}, {})",
            self.with(&self.item.res_impure),
            self.with(&self.item.res_pure)
        )
    }
}

impl<'a> Display for VmirDisplay<'a, heap_exp::InstKind> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            heap_exp::InstKind::Unary(op, val) => {
                let val_display = self.with(val);
                write!(f, "{:?}({})", op, val_display)
            }
            heap_exp::InstKind::Binary(op, lhs, rhs) => {
                let lhs_display = self.with(lhs);
                let rhs_display = self.with(rhs);
                write!(f, "{:?}({}, {})", op, lhs_display, rhs_display)
            }
            heap_exp::InstKind::Ternary(cond, then_val, else_val) => {
                let cond_display = self.with(cond);
                let then_display = self.with(then_val);
                let else_display = self.with(else_val);
                write!(
                    f,
                    "({} ? {} : {})",
                    cond_display, then_display, else_display
                )
            }
            heap_exp::InstKind::Call(func_id, args) => {
                let func_name = self.interner.resolve(func_id);
                write!(f, "{}(", func_name)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    let arg_display = self.with(arg);
                    write!(f, "{}", arg_display)?;
                }
                write!(f, ")")
            }
            heap_exp::InstKind::Deref(heap, val) => {
                write!(f, "*[{}]{}", self.with(heap), self.with(val))
            }
            heap_exp::InstKind::Perm(heap, loc) => {
                write!(f, "perm [{}] {}", self.with(heap), self.with(loc))
            }
            heap_exp::InstKind::Acc(heap, loc, amt) => {
                write!(
                    f,
                    "{} ** acc({}, {})",
                    self.with(heap),
                    self.with(loc),
                    self.with(amt)
                )
            }
        }
    }
}

impl<'a> Display for VmirDisplay<'a, heap_exp::Value> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            heap_exp::Value::Temp(idx) => write!(f, "e{idx}"),
            heap_exp::Value::Literal(lit) => {
                write!(f, "{}", self.with(lit))
            }
        }
    }
}

impl<'a> Display for VmirDisplay<'a, heap_exp::Literal> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            heap_exp::Literal::Int(i) => write!(f, "{}", i),
            heap_exp::Literal::Bool(b) => write!(f, "{}", b),
            heap_exp::Literal::Null => write!(f, "null"),
            heap_exp::Literal::Real(r) => write!(f, "{}", r),
            heap_exp::Literal::EmptyHeap => write!(f, "∅"),
        }
    }
}

impl<'a> Display for VmirDisplay<'a, method_ir::Method> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for (idx, method_ir::Inst { kind, ty }) in self.item.0.iter().enumerate() {
            self.write_indent(f)?;
            writeln!(f, "e{idx}: {} := {}", self.with(ty), self.with(kind))?;
        }
        Ok(())
    }
}

impl<'a> Display for VmirDisplay<'a, method_ir::InstKind> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            method_ir::InstKind::Fresh => write!(f, "fresh"),
            method_ir::InstKind::UnOp(op, val) => {
                write!(f, "{:?}({})", op, self.with(val))
            }
            method_ir::InstKind::BinOp(op, lhs, rhs) => {
                write!(f, "{:?}({}, {})", op, self.with(lhs), self.with(rhs))
            }
            method_ir::InstKind::HeapOp(op, member, args) => {
                let method_name = self.interner.resolve(member);
                write!(f, "{} {}(", self.with(op), method_name)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", self.with(arg))?;
                }
                write!(f, ")")
            }
            method_ir::InstKind::HeapAssign(heap, addr, val) => {
                write!(
                    f,
                    "assign[{}]({}, {})",
                    self.with(heap),
                    self.with(addr),
                    self.with(val)
                )
            }
        }
    }
}

impl<'a> Display for VmirDisplay<'a, method_ir::HeapOp> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            method_ir::HeapOp::Inhale => write!(f, "inhale"),
            method_ir::HeapOp::Exhale => write!(f, "exhale"),
        }
    }
}

// impl<'a> Display for VmirDisplay<'a, StmtBlock> {
//     fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
//         for stmt in &self.item.0 {
//             let stmt_display = self.with(stmt);
//             writeln!(f, "{}", stmt_display)?;
//         }
//         Ok(())
//     }
// }

impl<'a> Display for VmirDisplay<'a, Type> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            Type::Bool => write!(f, "Bool"),
            Type::Int => write!(f, "Int"),
            Type::Real => write!(f, "Real"),
            Type::Ref => write!(f, "Ref"),
            Type::Domain(id) => {
                let name = self.interner.resolve(id);
                write!(f, "{}", name)
            }
            Type::Addr(ty) => write!(f, "&{}", self.with(ty.as_ref())),
            Type::Heap => write!(f, "Heap"),
        }
    }
}

impl<'a> Display for VmirDisplay<'a, IdnDecl> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.with(&self.item.0))
    }
}

impl<'a> Display for VmirDisplay<'a, Ident> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.item.0)
    }
}
