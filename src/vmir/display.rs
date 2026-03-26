use crate::vmir::ast::*;
use std::fmt::{self, Display, Formatter};

impl Display for Program {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for (_, decl) in self.0.iter_enumerated() {
            writeln!(f, "{}", decl)?;
            writeln!(f)?; // Empty line between declarations
        }
        Ok(())
    }
}

impl Display for Declaration {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Declaration::Domain => write!(f, "// Domain"),
            Declaration::DomainElement => write!(f, "// DomainElement"),
            Declaration::Function(func) => write!(f, "{}", func),
            Declaration::Method(method) => write!(f, "{}", method),
            Declaration::Resource(resource) => write!(f, "{}", resource),
            Declaration::Adt => write!(f, "// Adt"),
            Declaration::AdtConstructor => write!(f, "// AdtConstructor"),
        }
    }
}

impl Display for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "function {}", self.signature.name)?;
        write!(f, "(")?;
        for (i, arg) in self.args().iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", arg)?;
        }
        write!(f, ")")?;

        if !self.ret().is_empty() {
            write!(f, ": ")?;
            if self.ret().len() == 1 {
                write!(f, "{}", self.ret()[0])?;
            } else {
                write!(f, "(")?;
                for (i, ret) in self.ret().iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", ret)?;
                }
                write!(f, ")")?;
            }
        }

        if self.body.is_some() {
            writeln!(f, " {{")?;
            writeln!(f, "  // body")?;
            write!(f, "}}")?;
        }

        Ok(())
    }
}

impl Display for Method {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "method {}", self.signature.name)?;
        write!(f, "(")?;
        for (i, arg) in self.args().iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", arg)?;
        }
        write!(f, ")")?;

        if !self.ret().is_empty() {
            write!(f, ": ")?;
            if self.ret().len() == 1 {
                write!(f, "{}", self.ret()[0])?;
            } else {
                write!(f, "(")?;
                for (i, ret) in self.ret().iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", ret)?;
                }
                write!(f, ")")?;
            }
        }

        if self.body.is_some() {
            writeln!(f, " {{")?;
            writeln!(f, "  // body")?;
            write!(f, "}}")?;
        }

        Ok(())
    }
}

impl Display for Resource {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "resource {}", self.name)?;
        write!(f, "(")?;
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", arg)?;
        }
        write!(f, ")")?;

        if self.body.is_some() {
            writeln!(f, " {{")?;
            writeln!(f, "  // permissions")?;
            writeln!(f, "}} with {{")?;
            writeln!(f, "  // assertions")?;
            write!(f, "}}")?;
        }

        Ok(())
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Type::Bool => write!(f, "Bool"),
            Type::Int => write!(f, "Int"),
            Type::Real => write!(f, "Real"),
            Type::Ref => write!(f, "Ref"),
            Type::Domain => write!(f, "Domain"),
            Type::Addr(ty) => write!(f, "&{}", ty),
            Type::Resource(name) => write!(f, "{}", name),
        }
    }
}

impl Display for IdnDecl {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for Ident {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// Helper methods to access signature fields
impl Function {
    fn args(&self) -> &Vec<Type> {
        &self.signature.args
    }

    fn ret(&self) -> &Vec<Type> {
        &self.signature.ret
    }
}

impl Method {
    fn args(&self) -> &Vec<Type> {
        &self.signature.args
    }

    fn ret(&self) -> &Vec<Type> {
        &self.signature.ret
    }
}
