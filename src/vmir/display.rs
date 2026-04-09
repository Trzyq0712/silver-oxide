use crate::vmir::ast::*;
use crate::vmir::impure;
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
        for (_, decl) in self.decls.iter_enumerated() {
            let display = VmirDisplay::new(decl, &self.interner);
            writeln!(f, "{}", display)?;
            writeln!(f)?; // Empty line between declarations
        }
        Ok(())
    }
}

impl<'a> Display for VmirDisplay<'a, Declaration> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            Declaration::Domain(domain) => {
                let name = self.interner.resolve(&domain.name);
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
        let contract_display = self.with_indent(&self.item.contract);
        writeln!(f, "{}", contract_display)?;

        if let Some(ref body) = self.item.body {
            self.write_indent(f)?;
            writeln!(f, "{{")?;
            let body_display = self.with_indent(body);
            // write!(f, "{}", body_display)?;
            self.write_indent(f)?;
            writeln!(f, "}}")?;
        }

        Ok(())
    }
}

impl<'a> Display for VmirDisplay<'a, MethContract> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if let Some(requires) = &self.item.requires {
            self.write_indent(f)?;
            writeln!(f, "requires")?;
            write!(f, "{}", self.with_indent(requires))?
        }
        if let Some(ensures) = &self.item.ensures {
            self.write_indent(f)?;
            writeln!(f, "ensures")?;
            write!(f, "{}", self.with_indent(ensures))?
        }
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

impl<'a> Display for VmirDisplay<'a, impure::HeapExp> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // Display input signatures
        if !self.item.input_types.is_empty() {
            self.write_indent(f)?;
            write!(f, "inputs: [")?;
            for (i, ty) in self.item.input_types.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", self.with(ty))?;
            }
            writeln!(f, "]")?;
        }

        // Display the SSA instructions
        for (idx, impure::Inst { kind, ty }) in self.item.insts.iter().enumerate() {
            self.write_indent(f)?;
            writeln!(f, "e{}: {} := {}", idx, self.with(ty), self.with(kind))?;
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

impl<'a> Display for VmirDisplay<'a, impure::InstKind> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            impure::InstKind::Unary(op, val) => {
                let val_display = self.with(val);
                write!(f, "{:?}({})", op, val_display)
            }
            impure::InstKind::Binary(op, lhs, rhs) => {
                let lhs_display = self.with(lhs);
                let rhs_display = self.with(rhs);
                write!(f, "{:?}({}, {})", op, lhs_display, rhs_display)
            }
            impure::InstKind::Ternary(cond, then_val, else_val) => {
                let cond_display = self.with(cond);
                let then_display = self.with(then_val);
                let else_display = self.with(else_val);
                write!(
                    f,
                    "({} ? {} : {})",
                    cond_display, then_display, else_display
                )
            }
            impure::InstKind::Call(func_id, args) => {
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
            impure::InstKind::Deref(heap, val) => {
                write!(f, "*[{}]{}", self.with(heap), self.with(val))
            }
            impure::InstKind::Read(local) => {
                write!(f, "read {}", self.with(local))
            }
            impure::InstKind::Perm(heap, loc) => {
                write!(f, "perm [{}] {}", self.with(heap), self.with(loc))
            }
            impure::InstKind::PermOp(heap, perm_op) => {
                match perm_op {
                    impure::PermOp::Adjust(loc, amt) => {
                        write!(
                            f,
                            "perm_op [{}] {} by {}",
                            self.with(heap),
                            self.with(loc),
                            self.with(amt)
                        )
                    }
                }
            }
        }
    }
}

impl<'a> Display for VmirDisplay<'a, impure::Value> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            impure::Value::Temp(idx) => write!(f, "e{}", idx.0),
            impure::Value::Literal(lit) => {
                write!(f, "{}", self.with(lit))
            }
        }
    }
}

impl<'a> Display for VmirDisplay<'a, impure::Local> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", &self.item.0)
    }
}

impl<'a> Display for VmirDisplay<'a, impure::Literal> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.item {
            impure::Literal::Int(i) => write!(f, "{}", i),
            impure::Literal::Bool(b) => write!(f, "{}", b),
            impure::Literal::Null => write!(f, "null"),
            impure::Literal::Real(r) => write!(f, "{}", r),
            impure::Literal::EmptyHeap => write!(f, "∅"),
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
