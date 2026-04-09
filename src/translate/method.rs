use nonmax::NonMaxU32;
use num::traits::identities;
use rusttyc::TypeChecker;

use crate::{
    silver,
    translate::{exp::ExpTranslationContext, typecheck, VmirTranslator},
    vmir::{self, Value},
    HashMap,
};

/// Context for translating method bodies
pub struct MethodTranslationContext<'a, 'b> {
    /// Maps Silver variable names to (VMIR local index, type)
    env: HashMap<&'b str, (NonMaxU32, vmir::Type)>,
    /// Counter for generating temporary indices
    temp_counter: u32,
    /// Accumulated statements in the method body
    statements: Vec<vmir::Statement>,

    tc: TypeChecker<typecheck::TcType, vmir::impure::Value>,
    /// Reference to the translator for looking up global names
    translator: &'a VmirTranslator,
}

impl<'a, 'b> MethodTranslationContext<'a, 'b> {
    pub fn new(
        translator: &'a VmirTranslator,
        env: impl IntoIterator<Item = (&'b silver::IdnDecl, vmir::Type)>,
    ) -> Self {
        let env: HashMap<&'b str, (NonMaxU32, vmir::Type)> = env
            .into_iter()
            .enumerate()
            .map(|(idx, (name, ty))| {
                let idx = NonMaxU32::new(idx as u32).expect("Too many parameters");
                (name.0 .0.as_str(), (idx, ty.into()))
            })
            .collect();

        let mut tc = TypeChecker::new();
        // Impose the typechecker constraints
        for (idx, ty) in env.values() {
            let key = tc.get_var_key(&vmir::Local(*idx).into());
            tc.impose(key.concretizes_explicit(ty.into())).unwrap()
        }

        Self {
            env: HashMap::new(),
            temp_counter: 0,
            statements: Vec::new(),
            tc,
            translator,
        }
    }

    fn add_inst() {}

    pub fn add_statement(&mut self, stmt: &silver::Statement) {
        match stmt {
            silver::Statement::Assign(lhs, rhs) => {}
            _ => unimplemented!(),
        }
    }

    fn translate_assign_rhs(
        &mut self,
        assign_rhs: &silver::AssignRhs,
        tys: &[vmir::Type],
    ) -> Vec<vmir::impure::Value> {
        match assign_rhs {
            silver::AssignRhs::Exp(e) => {
                assert_eq!(tys.len(), 1);
                vec![self.translate_exp(e, tys[0])]
            }
            silver::AssignRhs::Call(ident, args) => unimplemented!(),
            silver::AssignRhs::New(_) => unimplemented!(),
        }
    }

    fn translate_exp(&mut self, exp: &silver::ExpKind, ty: &vmir::Type) -> vmir::impure::Value {
        let ctx = ExpTranslationContext::with_env(self.translator, self.env.clone());

        ctx.translate_exp(exp, ty)
    }

    pub fn translate(mut self) {}
}
