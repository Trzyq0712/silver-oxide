use crate::{
    verify::{analysis::ConstFold, lang::Symbolic, rewrite},
    vmir::{Literal, MemberId, Polarity, Type},
};
use lasso::Rodeo;

pub(crate) struct VerifyContext<'a> {
    pub(crate) egraph: egg::EGraph<Symbolic, ConstFold>,
    rules: Vec<egg::Rewrite<Symbolic, ConstFold>>,
    fresh_counter: usize,
    pub(crate) interner: &'a Rodeo<MemberId>,
}

impl<'a> VerifyContext<'a> {
    pub(crate) fn new(interner: &'a Rodeo<MemberId>) -> Self {
        Self {
            egraph: egg::EGraph::default(),
            rules: rewrite::rules(),
            fresh_counter: 0,
            interner,
        }
    }

    /// Run rewrite saturation over the e-graph in place.
    pub(crate) fn saturate(&mut self) {
        let egraph = std::mem::take(&mut self.egraph);
        let runner = egg::Runner::default().with_egraph(egraph).run(&self.rules);
        self.egraph = runner.egraph;
    }

    pub(crate) fn add(&mut self, node: Symbolic) -> egg::Id {
        self.egraph.add(node)
    }

    pub(crate) fn fresh_symbolic_value(&mut self, ty: Type) -> egg::Id {
        let id = self.fresh_counter as u32;
        self.fresh_counter += 1;
        self.egraph.add(Symbolic::Fresh(id, ty))
    }

    /// Build `antecedents ==> consequent` as a right-associative chain of `Ite`
    /// muxers with fallback `true` (vacuous truth). No boolean AND tree.
    /// `antecedents` must be in innermost-first fold order. A positive literal
    /// puts the running term in the true-branch (`true` in the false-branch); a
    /// negative literal swaps the branches.
    pub(crate) fn implication(
        &mut self,
        consequent: egg::Id,
        antecedents: impl Iterator<Item = (egg::Id, Polarity)>,
    ) -> egg::Id {
        let true_ = self.add(Symbolic::Lit(Literal::Bool(true)));
        let mut imp = consequent;
        for (id, pol) in antecedents {
            imp = match pol {
                Polarity::Positive => self.add(Symbolic::Ite(Type::Bool, [id, imp, true_])),
                Polarity::Negative => self.add(Symbolic::Ite(Type::Bool, [id, true_, imp])),
            };
        }
        imp
    }

    /// Prove `goal == true` under the hypotheses `pc_lits`, using a throwaway
    /// clone of the e-graph so the assumptions never touch live state. On
    /// success, commit the proven implication `pc ==> goal` into the live graph
    /// (so it can fire later once the PC is established) and return `true`.
    ///
    /// A PC literal whose value already folds to the opposite boolean means the
    /// path is unsatisfiable: the goal then holds vacuously, so we short-circuit
    /// to `true` (and still commit the vacuously-true implication). This also
    /// avoids `ConstFold`'s conflicting-value panic when unioning into the
    /// `true`/`false` eclass.
    pub(crate) fn prove_under_pc(
        &mut self,
        goal: egg::Id,
        pc_lits: &[(egg::Id, Polarity)],
    ) -> bool {
        let mut probe = self.egraph.clone();
        let true_ = probe.add(Symbolic::Lit(Literal::Bool(true)));
        let false_ = probe.add(Symbolic::Lit(Literal::Bool(false)));

        let mut proven = false;
        let mut unsat_pc = false;
        for (id, pol) in pc_lits {
            let want_true = matches!(pol, Polarity::Positive);
            match &probe[*id].data.value {
                Some(Literal::Bool(b)) if *b != want_true => {
                    // PC literal contradicts its required polarity → off-path.
                    unsat_pc = true;
                    break;
                }
                _ => {
                    probe.union(*id, if want_true { true_ } else { false_ });
                }
            }
        }

        if unsat_pc {
            proven = true;
        } else {
            let runner = egg::Runner::default()
                .with_egraph(probe)
                .run(&self.rules);
            let probe = runner.egraph;
            if probe.find(goal) == probe.find(true_) {
                proven = true;
            }
        }

        if proven {
            let imp = self.implication(goal, pc_lits.iter().rev().copied());
            let true_live = self.add(Symbolic::Lit(Literal::Bool(true)));
            self.egraph.union(imp, true_live);
            self.egraph.rebuild();
        }
        proven
    }
}
