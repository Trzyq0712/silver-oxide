mod adt;
mod analyze;
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

pub use heap::{Assign, HeapInst, HeapVal, Sign};
pub use pure::{BinOp, FALSE, Literal, NULL, PureInst, TRUE, Val, none, write};

pub use adt::{Adt, AdtMeta, ResourceMeta};
pub use analyze::{AnalysisError, AnalyzedProgram, DepGraph, analyze};
pub use domain::Domain;
pub use function::{Bound, Function, FunctionCall, Location};
pub use inst::{Inst, InstKind, PathConds, Polarity};
pub use method::Method;
pub use resource::{Precond, Resource, ResourceBody, ResourceCall};

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
    pub adt_meta: AdtMeta,
    /// Per-resource `fold`/`unfold` metadata, keyed by resource `MemberId`.
    pub resource_meta: std::collections::HashMap<MemberId, ResourceMeta>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Declaration {
    Domain(Domain),
    Function(Function),
    Location(Location),
    Method(Method),
    Resource(Resource),
    Adt(Adt),
}
