use crate::vmir::{exp::Exp, Local, Type};
use derive_more::{From, Into};
use lasso::{Key, Rodeo};
use nonmax::NonMaxU32;
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
    Adt(Adt),
    AdtConstructor,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Method {
    pub name: MemberId,
    pub signature: MethSig,
    pub contract: MethContract,
    pub body: Option<StmtBlock>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Resource {
    pub name: MemberId,
    pub args: Vec<Type>,
    pub snapshot: MemberId,
    pub body: Option<Exp>,
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
    pub body: Option<Exp>,
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
    pub requires: Option<Exp>,
    pub ensures: Option<Exp>,
}

impl MethContract {
    pub fn empty() -> Self {
        Self {
            requires: None,
            ensures: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncContract {
    pub requires: Option<Exp>,
    pub ensures: Option<Exp>,
}

impl FuncContract {
    pub fn empty() -> Self {
        Self {
            requires: None,
            ensures: None,
        }
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
    /// x, y := m(a, b, c)
    MethodCall(Vec<AssignTarget>, MemberId, Vec<Local>),
    /// Assign to a local or a temporary
    /// x := e
    /// x: T, e: T
    Assign(AssignTarget, Exp),
    /// Assign to a heap location
    /// x *= e
    /// x: &T, e: T
    HeapAssign(AssignTarget, Exp),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AssignTarget {
    /// Named local variable
    Local(NonMaxU32),
    /// Anonymous temporary
    Temp(NonMaxU32),
}
