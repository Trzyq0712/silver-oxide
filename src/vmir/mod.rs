mod adt;
mod domain;
mod function;
mod heap;
mod inst;
mod method;
mod pure;
mod resource;
mod ty;

pub mod display;

pub use ty::Type;

pub use heap::{Acc, HeapInst, HeapVal};
pub use pure::{BinOp, FALSE, Literal, NULL, PureInst, TRUE, Val, none, write};

pub use adt::Adt;
pub use domain::Domain;
pub use function::{Function, FunctionCall};
pub use inst::{Bumps, Inst, InstContext, InstKind, PathConds, Polarity, UsesPc};
pub use method::{Assign, HeapExt, InstExt, Method, MethodCtx, MethodInst, PureExt};
pub use resource::{
    Resource, ResourceBody, ResourceCall, ResourceCtx, ResourceInst, ResourcePureExt,
};

use derive_more::{From, Into};
use lasso::{Key, Rodeo};
use typed_index_collections::TiVec;

#[derive(Debug, From, Into, Eq, PartialEq, PartialOrd, Ord, Hash, Clone, Copy)]
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
