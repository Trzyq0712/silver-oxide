use crate::{
    verify::lang::Symbolic,
    vmir::{self, MemberId},
};
use lasso::Rodeo;

pub(crate) struct VerifyContext<'a> {
    pub(crate) egraph: egg::EGraph<Symbolic, ()>,
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

    pub(crate) fn fresh_symbolic_value(&mut self, prefix: &str) -> egg::Id {
        let symbol = egg::Symbol::from(format!("{prefix}#{}", self.fresh_counter));
        self.fresh_counter += 1;
        self.egraph.add(Symbolic::Fresh(symbol))
    }

    pub(crate) fn fresh_for_type(&mut self, ty: &vmir::Type) -> egg::Id {
        self.fresh_symbolic_value(&ty.to_string())
    }
}
