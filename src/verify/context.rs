use crate::{
    verify::{analysis::ConstFold, lang::Symbolic},
    vmir::{MemberId, Type},
};
use lasso::Rodeo;

pub(crate) struct VerifyContext<'a> {
    pub(crate) egraph: egg::EGraph<Symbolic, ConstFold>,
    fresh_counter: usize,
    pub(crate) interner: &'a Rodeo<MemberId>,
}

impl<'a> VerifyContext<'a> {
    pub(crate) fn new(interner: &'a Rodeo<MemberId>) -> Self {
        Self {
            egraph: egg::EGraph::default(),
            fresh_counter: 0,
            interner,
        }
    }

    pub(crate) fn add(&mut self, node: Symbolic) -> egg::Id {
        self.egraph.add(node)
    }

    pub(crate) fn fresh_symbolic_value(&mut self, ty: Type) -> egg::Id {
        let id = self.fresh_counter as u32;
        self.fresh_counter += 1;
        self.egraph.add(Symbolic::Fresh(id, ty))
    }
}
