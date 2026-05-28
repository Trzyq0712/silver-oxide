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
pub use pure::{BinOp, FALSE, FunctionCall, Literal, NULL, PureInst, TRUE, UnOp, Val, none, write};

pub use adt::Adt;
pub use domain::Domain;
pub use function::Function;
pub use inst::{Context, Inst, InstKind, Lit, PathCond};
pub use method::{Method, MethodCtx, MethodHeapVal, MethodInst, MethodInstExt};
pub use resource::{
    Resource, ResourceBody, ResourceCall, ResourceCtx, ResourceHeapVal, ResourceInst,
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
