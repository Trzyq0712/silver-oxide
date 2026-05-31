use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Statement {
    Assume(Exp),
    Assert(Exp),
    Refute(Exp),
    Inhale(Exp),
    Exhale(Exp),
    Fold(AccExp),
    Unfold(AccExp),
    Goto(Ident),
    Label(IdnDecl, Vec<Invariant>),
    Var(Vec<IdnDeclTyped>, Option<AssignRhs>),
    While(Exp, Vec<Invariant>, Vec<Decreases>, StmtBlock),
    If(Exp, StmtBlock, Option<StmtBlock>),
    // Package(AccExp, Option<StmtBlock>),
    // Apply(AccExp),
    Assign(Vec<AssignLhs>, AssignRhs),
    Block(StmtBlock),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AssignLhs {
    Ident(Ident),
    Field(Exp, Ident),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AssignRhs {
    Exp(Exp),
    Call(Call<StmtCallKind>),
    New(StarOrNames),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum StarOrNames {
    Star,
    Names(Vec<Ident>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Invariant(pub Exp);
