use lasso::Spur;

// ==========================================
// 1. Core Primitives & Types
// ==========================================

/// A resolved identifier string.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ident(pub Spur);

/// An identifier bundled with its explicit type (e.g., `x: Int`).
pub struct TypedIdent {
    pub name: Ident,
    pub ty: Type,
}

pub enum BuiltinCollection {
    Seq(Box<Type>),
    Set(Box<Type>),
    MultiSet(Box<Type>),
    Map(Box<Type>, Box<Type>),
}

pub enum Type {
    Bool,
    Int,
    Real,
    Ref,
    Collection(BuiltinCollection),
    Domain(Ident, Vec<Type>),
}

pub enum UnOp {
    Not,
    Neg,
    Cardinality,
}
pub enum BinOp {
    Or,
    And,
    Implies,
    Iff,
    Eq,
    Neq,

    Lt,
    Le,
    Gt,
    Ge,

    Plus,
    Minus,
    Mult,
    Div,
    Mod,
    In,
    Union,
    SetMinus,
    Intersection,
    Subset,
    Concat,
    Range,
}

pub enum Literal {
    Bool(bool),
    Int(num::BigInt),
    Real(num::BigRational),
    Null,
    Wildcard,
}

// ==========================================
// 2. Pure Expressions
// ==========================================

/// A pure expression bundled with its synthesized type.
pub struct TypedPureExp<Ext> {
    pub ty: Type,
    pub exp: Box<PureExpKind<Ext>>,
}

/// A generic function or predicate call.
pub struct Call<Ext> {
    pub name: Ident,
    pub args: Vec<TypedPureExp<Ext>>,
}

/// The variants of a purely mathematical/logical expression.
/// The `Ext` generic dictates which context-specific nodes are allowed.
pub enum PureExpKind<Ext> {
    Ident(Ident),
    Const(Literal),
    Unary(UnOp, TypedPureExp<Ext>),
    Binary(BinOp, TypedPureExp<Ext>, TypedPureExp<Ext>),
    Ternary {
        if_: TypedPureExp<Ext>,
        then: TypedPureExp<Ext>,
        else_: TypedPureExp<Ext>,
    },
    /// Evaluates `exp` under the temporary unfolding of the predicate.
    Unfolding(PredicateWithPerm<Ext>, TypedPureExp<Ext>),
    FunctionCall(Call<Ext>),
    LetIn {
        binder: Ident,
        value: TypedPureExp<Ext>,
        exp: TypedPureExp<Ext>,
    },
    Ascribe(TypedPureExp<Ext>, Type),
    /// A pure projection from an ADT/Domain.
    AdtDestructor(TypedPureExp<Ext>, Ident),
    /// A variant check on an ADT (e.g., `e.isCons(list)`).
    AdtDiscriminator(TypedPureExp<Ext>, Ident),
    /// The context-specific extension (e.g., `old`, `perm`, `result`).
    Ext(Ext),
}

// ==========================================
// 3. Spatial & Resource Expressions
// ==========================================

/// An expression that asserts or transfers heap resources.
pub struct SpatialExp<PureExt>(pub Box<SpatialExpKind<PureExt>>);

pub enum SpatialExpKind<PureExt> {
    Implies(TypedPureExp<PureExt>, SpatialExp<PureExt>),
    Conj(SpatialExp<PureExt>, SpatialExp<PureExt>),
    Ternary {
        if_: TypedPureExp<PureExt>,
        then: SpatialExp<PureExt>,
        else_: SpatialExp<PureExt>,
    },
    /// Represents `acc(resource, perm)`.
    Acc(ResourceExp<PureExt>, TypedPureExp<PureExt>),
    /// Lifts a pure boolean expression into the spatial context.
    Pure(TypedPureExp<PureExt>),
}

/// The valid targets for acc or perm queries.
pub struct ResourceExp<PureExt>(pub Box<ResourceExpKind<PureExt>>);

pub enum ResourceExpKind<PureExt> {
    /// A mutable heap location: `e.f`
    Field(TypedPureExp<PureExt>, Ident),
    /// A spatial predicate: `P(args)`
    PredicateCall(Call<PureExt>),
}

/// A predicate call bundled with an explicit permission amount.
pub struct PredicateWithPerm<PureExt> {
    pub pred_call: Call<PureExt>,
    pub perm: TypedPureExp<PureExt>,
}

// ==========================================
// 4. Context Extensions
// ==========================================

/// Extensions allowed *only* in pure function postconditions.
pub enum FuncEnsuresExt {
    Result,
    Old(TypedPureExp<FuncEnsuresExt>),
}

/// Extensions allowed *only* in method postconditions.
pub enum MethodEnsuresExt {
    Old(TypedPureExp<MethodEnsuresExt>),
}

/// Extensions allowed *only* in imperative method bodies.
pub enum MethodBodyExt {
    Old(Option<Spur>, TypedPureExp<MethodBodyExt>),
    Perm(ResourceExp<MethodBodyExt>),
}

// ==========================================
// 5. Statements & Imperative Blocks
// ==========================================

pub type PureMethodExp = TypedPureExp<MethodBodyExt>;
pub type SpatialMethodExp = SpatialExp<MethodBodyExt>;

pub struct StmtBlock(pub Vec<Statement>);

pub enum Statement {
    Assume(SpatialMethodExp),
    Assert(SpatialMethodExp),
    Inhale(SpatialMethodExp),
    Exhale(SpatialMethodExp),
    If(PureMethodExp, StmtBlock, Option<StmtBlock>),
    /// Variable declaration (e.g., `var x: Int := 5`)
    Var(Vec<TypedIdent>, Option<AssignRhs>),
    /// Imperative assignment (e.g., `x, y.f := 1, 2`)
    Assign(Vec<AssignLhs>, AssignRhs),
    Block(StmtBlock),
    Fold(PredicateWithPerm<MethodBodyExt>),
    Unfold(PredicateWithPerm<MethodBodyExt>),
}

pub enum AssignLhs {
    /// Field assignment to `e.f` where `e` is of type `Ref`.
    Field(PureMethodExp, Ident),
    /// Local variable assignment.
    Var(Ident),
}

pub enum AssignRhs {
    /// E.g., `new(*)` or `new(f1, f2)`
    New(StarOrFields),
    MethodCall(Call<MethodBodyExt>),
    Exp(PureMethodExp),
}

pub enum StarOrFields {
    Star,
    Fields(Vec<Ident>),
}

// ==========================================
// 6. Top-Level Declarations
// ==========================================

pub enum Declaration {
    Function(Function),
    Predicate(Predicate),
    Method(Method),
    Field(Field),
}

pub struct Field(pub TypedIdent);

/// A purely mathematical function that cannot mutate state.
pub struct Function {
    pub name: Ident,
    pub params: Vec<TypedIdent>,
    pub ret: Type,
    pub requires: Option<SpatialExp<!>>,
    pub ensures: Option<TypedPureExp<FuncEnsuresExt>>,
    pub body: Option<TypedPureExp<!>>,
}

/// An imperative sub-routine that can mutate the heap.
pub struct Method {
    pub name: Ident,
    pub params: Vec<TypedIdent>,
    pub rets: Vec<TypedIdent>,
    pub requires: Option<SpatialExp<!>>,
    pub ensures: Option<SpatialExp<MethodEnsuresExt>>,
    pub body: Option<StmtBlock>,
}

/// A spatial macro representing a fraction of the heap.
pub struct Predicate {
    pub name: Ident,
    pub params: Vec<TypedIdent>,
    pub body: Option<SpatialExp<!>>,
}
