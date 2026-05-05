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

pub use inst::{Inst, ResourceCall};
pub use ty::Type;

pub use heap::{Acc, HeapInst, HeapVal};
pub use pure::{none, write, BinOp, FunctionCall, Literal, PureInst, UnOp, Val, FALSE, NULL, TRUE};

pub use adt::Adt;
pub use domain::Domain;
pub use function::Function;
pub use method::Method;
pub use resource::Resource;

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
