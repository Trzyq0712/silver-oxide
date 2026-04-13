use crate::vmir::{heap_exp::HeapExp, Type};
use derive_more::{From, Into};
use lasso::{Key, Rodeo};
use nonmax::NonMaxU32;
use std::fmt::{Display, Formatter};
use typed_index_collections::TiVec;

#[derive(Debug, From, Into, Eq, PartialEq, Hash, Clone, Copy)]
pub struct MemberId(pub usize);

unsafe impl Key for MemberId {
    fn into_usize(self) -> usize {
        self.0
    }

    fn try_from_usize(int: usize) -> Option<Self> {
        Some(Self(int))
    }
}

#[derive(Debug, Clone)]
pub struct Program {
    pub decls: TiVec<MemberId, Declaration>,
    pub interner: Rodeo<MemberId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Declaration {
    Domain(Domain),
    DomainElement,
    Function(Function),
    Method(Method),
    Resource(Resource),
    HeapExp(HeapExp),
    Adt(Adt),
    AdtConstructor,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Method {
    pub name: MemberId,
    pub signature: MethSig,
    pub body: StmtBlock,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Resource {
    pub name: MemberId,
    pub args: Vec<Type>,
    pub snapshot: MemberId,
    pub body: Option<HeapExp>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Signature {
    pub args: Vec<Type>,
    pub ret: Vec<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncSig {
    pub args: Vec<Type>,
    pub ret: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MethSig {
    pub args: Vec<Type>,
    pub rets: Vec<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function {
    pub name: MemberId,
    pub signature: FuncSig,
    pub contract: FuncContract,
    pub body: Option<HeapExp>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Domain {
    pub name: MemberId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Adt {
    pub name: MemberId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MethContract {
    pub requires: HeapExp,
    pub ensures: HeapExp,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncContract {
    pub requires: Option<HeapExp>,
    pub ensures: Option<HeapExp>,
}

impl FuncContract {
    pub fn empty() -> Self {
        Self {
            requires: None,
            ensures: None,
        }
    }

    /// Create a contract with input signature metadata
    /// requires_inputs: [heap, ...args]
    /// ensures_inputs: [heap, old_heap, ...args]
    pub fn with_inputs(
        requires: Option<HeapExp>,
        ensures: Option<HeapExp>,
        requires_inputs: Vec<Type>,
        ensures_inputs: Vec<Type>,
    ) -> Self {
        let requires = requires.map(|mut exp| {
            exp.input_types = requires_inputs;
            exp
        });
        let ensures = ensures.map(|mut exp| {
            exp.input_types = ensures_inputs;
            exp
        });
        Self { requires, ensures }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExpBlock;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StmtBlock(pub Vec<Statement>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IdnDecl(pub Ident);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ident(pub String);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Statement {
    // /// x, y := m(a, b, c)
    // MethodCall(Vec<AssignTarget>, MemberId, Vec<Local>),
    // /// Assign to a local or a temporary
    // /// x := e
    // /// x: T, e: T
    // Assign(AssignTarget, HeapExp),
    // /// Assign to a heap location
    // /// x *= e
    // /// x: &T, e: T
    // HeapAssign(AssignTarget, HeapExp),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AssignTarget {
    /// Named local variable
    Local(NonMaxU32),
    /// Anonymous temporary
    Temp(NonMaxU32),
}

impl Display for IdnDecl {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for Ident {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "function f{}(", self.name.0)?;
        for (i, arg) in self.signature.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{arg}")?;
        }
        write!(f, "): {}", self.signature.ret)
    }
}

impl Display for Method {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "method m{}(", self.name.0)?;
        for (i, arg) in self.signature.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{arg}")?;
        }
        write!(f, ")")?;

        if !self.signature.rets.is_empty() {
            write!(f, " returns (")?;
            for (i, ret) in self.signature.rets.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{ret}")?;
            }
            write!(f, ")")?;
        }

        Ok(())
    }
}

impl Display for Resource {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "resource r{}(", self.name.0)?;
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{arg}")?;
        }
        write!(f, "): &d{}", self.snapshot.0)
    }
}
