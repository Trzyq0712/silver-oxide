use crate::vmir::Inst;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Method {
    pub insts: Vec<Inst>,
}
