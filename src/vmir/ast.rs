use derive_more::{From, Into};
use typed_index_collections::TiVec;

#[derive(Debug, From, Into, Eq, PartialEq, Hash, Clone, Copy)]
pub struct MemberId(usize);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Program(pub TiVec<MemberId, Declaration>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Declaration {
    Domain,
    DomainElement,
    Function(Function),
    Method(Method),
    Resource(Resource),
    Adt,
    AdtConstructor,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Method {
    pub signature: Signature,
    pub contract: Contract,
    pub body: Option<StmtBlock>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Resource {
    pub name: IdnDecl,
    pub args: Vec<Type>,
    pub body: Option<ResourceBody>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResourceBody {
    // Placeholder for resource body (permissions and assertions)
    // Will be expanded when we translate predicate bodies
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Signature {
    pub name: IdnDecl,
    pub args: Vec<Type>,
    pub ret: Vec<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function {
    pub signature: Signature,
    pub contract: Contract,
    pub body: Option<ExpBlock>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Contract;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExpBlock;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StmtBlock;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IdnDecl(pub Ident);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ident(pub String);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Bool,
    Int,
    Real,
    Ref,
    Domain,
    Addr(Box<Type>),
    Resource(Ident), // Resource type (e.g., pr_heap)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Statement {
    VarDecl(IdnDecl, Type),
    Assign(Vec<Ident>, Expr),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    Call(Ident, Vec<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
}
