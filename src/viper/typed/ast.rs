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

/// The type-parameter slot of a [`Type`]. Ground types use the uninhabited `!`
/// (no type parameters can appear); schema types inside an ADT/domain
/// declaration use [`Ident`] (a parameter reference).
pub trait TypeParam: Clone + std::fmt::Debug + PartialEq {
    /// The referenced parameter's name. Unreachable for the ground (`!`) slot.
    fn param(&self) -> Spur;
}

impl TypeParam for ! {
    fn param(&self) -> Spur {
        match *self {}
    }
}

impl TypeParam for Ident {
    fn param(&self) -> Spur {
        self.0
    }
}

/// An identifier bundled with its explicit type (e.g., `x: Int`).
#[derive(Debug, Clone, PartialEq)]
pub struct TypedIdent<G = !> {
    pub name: Ident,
    pub ty: Type<G>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BuiltinCollection<G = !> {
    Seq(Box<Type<G>>),
    Set(Box<Type<G>>),
    MultiSet(Box<Type<G>>),
    Map(Box<Type<G>>, Box<Type<G>>),
}

/// A Silver type. `G` is the type-parameter slot: `Type` (= `Type<!>`) is a
/// **ground** type — `Generic(!)` is uninhabited, so it provably has no type
/// parameters — while [`PolyType`] (`Type<Ident>`) is the **schema** form used
/// only inside ADT/domain declarations.
#[derive(Debug, Clone, PartialEq)]
pub enum Type<G = !> {
    Bool,
    Int,
    Real,
    Ref,
    Generic(G),
    Collection(BuiltinCollection<G>),
    Domain(Ident, Vec<Type<G>>),
}

/// A type that may reference type parameters — legal only inside ADT/domain
/// declarations.
pub type PolyType = Type<Ident>;

impl BuiltinCollection<Ident> {
    fn ground(&self) -> Option<BuiltinCollection> {
        Some(match self {
            BuiltinCollection::Seq(t) => BuiltinCollection::Seq(Box::new(t.ground()?)),
            BuiltinCollection::Set(t) => BuiltinCollection::Set(Box::new(t.ground()?)),
            BuiltinCollection::MultiSet(t) => BuiltinCollection::MultiSet(Box::new(t.ground()?)),
            BuiltinCollection::Map(k, v) => {
                BuiltinCollection::Map(Box::new(k.ground()?), Box::new(v.ground()?))
            }
        })
    }
}

impl PolyType {
    /// The ground form of this type, or `None` if it mentions a type parameter
    /// (`Generic`). The fallible boundary that enforces "no free type parameters
    /// outside an ADT/domain declaration".
    pub fn ground(&self) -> Option<Type> {
        Some(match self {
            Type::Bool => Type::Bool,
            Type::Int => Type::Int,
            Type::Real => Type::Real,
            Type::Ref => Type::Ref,
            Type::Generic(_) => return None,
            Type::Collection(c) => Type::Collection(c.ground()?),
            Type::Domain(id, args) => Type::Domain(
                *id,
                args.iter().map(PolyType::ground).collect::<Option<_>>()?,
            ),
        })
    }
}

impl From<&crate::viper::parsed::ast::Type> for PolyType {
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
    /// Domain functions are schemas over `type_params` — hence `Function<Ident>`.
    pub functions: Vec<Function<Ident>>,
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
    /// Field types are schemas over the ADT's `type_params` — hence the
    /// `Ident` slot.
    pub params: Vec<TypedIdent<Ident>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field(pub TypedIdent);

/// A purely mathematical function that cannot mutate state. `G` is the type slot
/// of the signature: a top-level Silver function is ground (`Function<!>`), a
/// domain function is a schema (`Function<Ident>`). Domain functions are
/// uninterpreted, so their contract/body fields are always `None`.
#[derive(Debug, Clone, PartialEq)]
pub struct Function<G = !> {
    pub name: Ident,
    pub params: Vec<TypedIdent<G>>,
    pub ret: Type<G>,
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
