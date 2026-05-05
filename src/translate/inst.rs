use crate::vmir;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UntypedInst {
    Assume(vmir::Val),
    Assert(vmir::Val),
    ResourceCall(vmir::ResourceCall),
    Heap(vmir::HeapInst),
    Pure(vmir::PureInst),
}
