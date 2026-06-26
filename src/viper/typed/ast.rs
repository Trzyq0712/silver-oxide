use lasso::Spur;

use crate::viper::Interner;

#[derive(Debug, PartialEq)]
pub struct Program {
    pub decls: Vec<Declaration>,
    /// The symbol alphabet every `Spur` in this program resolves through.
    pub interner: Interner,
}

/// A resolved identifier string.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ident(pub Spur);

/// An identifier bundled with its explicit type (e.g., `x: Int`).
#[derive(Debug, Clone, PartialEq)]
pub struct TypedIdent {
    pub name: Ident,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BuiltinCollection {
    Seq(Box<Type>),
    Set(Box<Type>),
    MultiSet(Box<Type>),
    Map(Box<Type>, Box<Type>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Bool,
    Int,
    Real,
    Ref,
    Generic(Ident),
    Collection(BuiltinCollection),
    Domain(Ident, Vec<Type>),
}

impl From<&crate::viper::parsed::ast::Type> for Type {
    fn from(t: &crate::viper::parsed::ast::Type) -> Self {
        use crate::viper::parsed::ast::Type as A;
        match t {
            A::Bool => Type::Bool,
            A::Int => Type::Int,
            A::Real => Type::Real,
            A::Ref => Type::Ref,
            A::Generic(id) => Type::Generic(Ident(id.id())),
            A::Domain(id, args) => {
                Type::Domain(Ident(id.id()), args.iter().map(Self::from).collect())
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum UnOp {
    Not,
    Neg,
    Cardinality,
}
#[derive(Debug, Clone, PartialEq)]
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

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Bool(bool),
    Int(num::BigInt),
    Real(num::BigRational),
    Null,
    Wildcard,
}

/// A pure expression bundled with its synthesized type.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedPureExp<Ext> {
    pub ty: Type,
    pub exp: Box<PureExpKind<Ext>>,
}

/// A generic function or predicate call.
#[derive(Debug, Clone, PartialEq)]
pub struct Call<Ext> {
    pub name: Ident,
    pub args: Vec<TypedPureExp<Ext>>,
}

/// The variants of a purely mathematical/logical expression.
/// The `Ext` generic dictates which context-specific nodes are allowed.
#[derive(Debug, Clone, PartialEq)]
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
    /// Heap field access: `e.f` where `f` is a Silver `field` declaration.
    Field(TypedPureExp<Ext>, Ident),
    LetIn {
        binder: Ident,
        value: TypedPureExp<Ext>,
        exp: TypedPureExp<Ext>,
    },
    Ascribe(TypedPureExp<Ext>, Type),
    /// Call to a top-level function
    FunctionCall(Call<Ext>),
    /// Call to a domain function
    DomainFunctionCall(DomainInstantiation, Call<Ext>),
    /// Constructor call of an ADT variant
    AdtConstructor(DomainInstantiation, Call<Ext>),
    /// A projection from an ADT.
    AdtDestructor(DomainInstantiation, TypedPureExp<Ext>, Ident),
    /// A variant check on an ADT (e.g., `e.isCons(list)`).
    AdtDiscriminator(DomainInstantiation, TypedPureExp<Ext>, Ident),
    /// The context-specific extension (e.g., `old`, `perm`, `result`).
    Ext(Ext),
}

/// A generic ADT/domain at a concrete instantiation — the monomorphization key.
/// `name` is the **head** declaration (the ADT/domain), distinct from the
/// `Call.name`/`Ident` that names the variant, field, or function at the use
/// site. The pre-lowering twin of `vmir::Type::Domain(MemberId, Vec<Type>)`.
#[derive(Debug, Clone, PartialEq)]
pub struct DomainInstantiation {
    pub name: Ident,
    pub type_args: Vec<Type>,
}

/// An expression that asserts or transfers heap resources.
#[derive(Debug, Clone, PartialEq)]
pub struct SpatialExp<PureExt>(pub Box<SpatialExpKind<PureExt>>);

#[derive(Debug, Clone, PartialEq)]
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
#[derive(Debug, Clone, PartialEq)]
pub struct ResourceExp<PureExt>(pub Box<ResourceExpKind<PureExt>>);

#[derive(Debug, Clone, PartialEq)]
pub enum ResourceExpKind<PureExt> {
    /// A mutable heap location: `e.f`
    Field(TypedPureExp<PureExt>, Ident),
    /// A spatial predicate: `P(args)`
    PredicateCall(Call<PureExt>),
}

/// A predicate call bundled with an explicit permission amount.
#[derive(Debug, Clone, PartialEq)]
pub struct PredicateWithPerm<PureExt> {
    pub pred_call: Call<PureExt>,
    pub perm: TypedPureExp<PureExt>,
}

/// Extensions allowed *only* in pure function postconditions.
#[derive(Debug, Clone, PartialEq)]
pub enum FuncEnsuresExt {
    Result,
    Old(TypedPureExp<FuncEnsuresExt>),
}

/// Extensions allowed *only* in method postconditions.
#[derive(Debug, Clone, PartialEq)]
pub enum MethodEnsuresExt {
    Old(TypedPureExp<MethodEnsuresExt>),
}

/// Extensions allowed *only* in imperative method bodies.
#[derive(Debug, Clone, PartialEq)]
pub enum MethodBodyExt {
    Old(Option<Spur>, TypedPureExp<MethodBodyExt>),
    Perm(ResourceExp<MethodBodyExt>),
}

pub type PureMethodExp = TypedPureExp<MethodBodyExt>;
pub type SpatialMethodExp = SpatialExp<MethodBodyExt>;

#[derive(Debug, Clone, PartialEq)]
pub struct StmtBlock(pub Vec<Statement>);

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    Assume(SpatialMethodExp),
    Assert(SpatialMethodExp),
    /// `refute A`: succeeds iff `A` is **not** provable in this state.
    Refute(SpatialMethodExp),
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
    /// Label marking a heap state for `old[L](...)` to refer back to; also a
    /// jump target for `goto`.
    Label(Spur),
    /// `goto L`: unconditional jump to the block labelled `L`.
    Goto(Spur),
}

#[derive(Debug, Clone, PartialEq)]
pub enum AssignLhs {
    /// Field assignment to `e.f` where `e` is of type `Ref`.
    Field(PureMethodExp, Ident),
    /// Local variable assignment.
    Var(Ident),
}

#[derive(Debug, Clone, PartialEq)]
pub enum AssignRhs {
    /// E.g., `new(*)` or `new(f1, f2)`
    New(StarOrFields),
    MethodCall(Call<MethodBodyExt>),
    Exp(PureMethodExp),
}

#[derive(Debug, Clone, PartialEq)]
pub enum StarOrFields {
    Star,
    Fields(Vec<Ident>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Declaration {
    Function(Function),
    Predicate(Predicate),
    Method(Method),
    Field(Field),
    Adt(Adt),
    Domain(Domain),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Domain {
    pub name: Ident,
    pub type_params: Vec<Ident>,
    pub functions: Vec<Function>,
    pub axioms: Vec<Axiom>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Axiom {
    pub name: Option<Ident>,
    pub exp: TypedPureExp<!>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Adt {
    pub name: Ident,
    pub type_params: Vec<Ident>,
    pub variants: Vec<AdtVariant>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AdtVariant {
    pub name: Ident,
    pub params: Vec<TypedIdent>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field(pub TypedIdent);

/// A purely mathematical function that cannot mutate state.
#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    pub name: Ident,
    pub params: Vec<TypedIdent>,
    pub ret: Type,
    pub requires: Option<SpatialExp<!>>,
    pub ensures: Option<TypedPureExp<FuncEnsuresExt>>,
    pub body: Option<TypedPureExp<!>>,
}

/// An imperative sub-routine that can mutate the heap.
#[derive(Debug, Clone, PartialEq)]
pub struct Method {
    pub name: Ident,
    pub params: Vec<TypedIdent>,
    pub rets: Vec<TypedIdent>,
    pub requires: Option<SpatialExp<!>>,
    pub ensures: Option<SpatialExp<MethodEnsuresExt>>,
    pub body: Option<StmtBlock>,
}

/// A spatial macro representing a fraction of the heap.
#[derive(Debug, Clone, PartialEq)]
pub struct Predicate {
    pub name: Ident,
    pub params: Vec<TypedIdent>,
    pub body: Option<SpatialExp<!>>,
}
