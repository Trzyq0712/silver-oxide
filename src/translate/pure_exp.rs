use rusttyc::{TcErr, TcKey, TypeChecker};

use crate::{
    silver,
    translate::{typecheck::TcType, VmirTranslator},
    vmir,
};

pub trait PureExpBackend {
    fn resolve_ident(&self, ident: &silver::Ident) -> vmir::Value;
    fn current_heap(&self) -> vmir::Value;
    fn emit_pure_inst(&mut self, inst: vmir::PureInst) -> vmir::Value;
    fn tc_mut(&mut self) -> &mut TypeChecker<TcType, vmir::Value>;
    fn translator(&self) -> &VmirTranslator;
}

pub struct PureExpTranslator<'a, B: PureExpBackend> {
    backend: &'a mut B,
}

impl<'a, B: PureExpBackend> PureExpTranslator<'a, B> {
    pub fn new(backend: &'a mut B) -> Self {
        Self { backend }
    }

    pub fn translate_pure_exp(
        &mut self,
        exp: &silver::PureExp,
    ) -> Result<vmir::Value, TcErr<TcType>> {
        self.translate_exp_kind(exp.as_ref())
    }

    pub fn translate_exp_kind(
        &mut self,
        exp: &silver::ExpKind,
    ) -> Result<vmir::Value, TcErr<TcType>> {
        use silver::ExpKind;
        match exp {
            ExpKind::Const(const_) => self.translate_const(const_),
            ExpKind::Ident(ident) => Ok(self.backend.resolve_ident(ident)),
            ExpKind::BinOp(op, left, right) => self.translate_binop(op, left, right),
            ExpKind::UnOp(op, e) => self.translate_unop(op, e),
            ExpKind::Ternary(cond, then, else_) => {
                let cond = self.translate_exp_kind(cond)?;
                let then = self.translate_exp_kind(then)?;
                let else_ = self.translate_exp_kind(else_)?;

                let cond_key = self.backend.tc_mut().get_var_key(&cond);
                let then_key = self.backend.tc_mut().get_var_key(&then);
                let else_key = self.backend.tc_mut().get_var_key(&else_);

                let val = self
                    .backend
                    .emit_pure_inst(vmir::PureInst::Ternary(cond, then, else_));
                let val_key = self.backend.tc_mut().get_var_key(&val);

                self.backend
                    .tc_mut()
                    .impose(cond_key.concretizes_explicit(TcType::Bool))?;
                self.backend
                    .tc_mut()
                    .impose(val_key.is_sym_meet_of(then_key, else_key))?;
                Ok(val)
            }
            ExpKind::FuncApp(func_name, args) => self.translate_func_app(func_name, args),
            ExpKind::Field(base, field_name) => {
                self.translate_func_app(field_name, &[base.clone()])
            }
            _ => unimplemented!("Expression translation: {:?}", exp),
        }
    }

    fn match_type(&mut self, ty: &vmir::Type, key: TcKey) -> Result<(), TcErr<TcType>> {
        self.backend
            .tc_mut()
            .impose(key.concretizes_explicit(ty.into()))?;
        match ty {
            vmir::Type::Addr(inner) => {
                let child = self.backend.tc_mut().get_child_key(key, 0)?;
                self.match_type(inner, child)
            }
            _ => Ok(()),
        }
    }

    fn translate_const(
        &mut self,
        const_: &silver::ConstKind,
    ) -> Result<vmir::Value, TcErr<TcType>> {
        let val = match const_ {
            silver::ConstKind::Bool(b) => vmir::Literal::Bool(*b),
            silver::ConstKind::Int(i) => vmir::Literal::Int(i.clone()),
            silver::ConstKind::Real(r) => vmir::Literal::Real(r.clone()),
            silver::ConstKind::Null => vmir::Literal::Null,
            _ => unimplemented!("Unsupported constant: {:?}", const_),
        }
        .into();
        let ty = match const_ {
            silver::ConstKind::Bool(_) => vmir::Type::Bool,
            silver::ConstKind::Int(_) => vmir::Type::Int,
            silver::ConstKind::Real(_) => vmir::Type::Real,
            silver::ConstKind::Null => vmir::Type::Ref,
            _ => unimplemented!(),
        };
        let key = self.backend.tc_mut().get_var_key(&val);
        self.backend
            .tc_mut()
            .impose(key.concretizes_explicit((&ty).into()))?;
        Ok(val)
    }

    fn translate_func_app(
        &mut self,
        func_name: &silver::Ident,
        args: &[silver::Exp],
    ) -> Result<vmir::Value, TcErr<TcType>> {
        let func_id = self
            .backend
            .translator()
            .interner()
            .get(&func_name.0)
            .unwrap_or_else(|| panic!("Function {} not found", func_name.0));

        let args = args
            .iter()
            .map(|arg| self.translate_exp_kind(arg))
            .collect::<Result<Vec<_>, _>>()?;

        let sig = self
            .backend
            .translator()
            .signatures()
            .function_sig(func_id)
            .clone();

        for (arg, ty) in args.iter().zip(sig.args.iter()) {
            let arg_key = self.backend.tc_mut().get_var_key(arg);
            self.match_type(ty, arg_key)?;
        }

        let val = self
            .backend
            .emit_pure_inst(vmir::PureInst::Call(func_id, args));
        let val_key = self.backend.tc_mut().get_var_key(&val);
        self.match_type(&sig.ret, val_key)?;
        Ok(val)
    }

    fn translate_binop(
        &mut self,
        op: &silver::BinOp,
        left: &silver::ExpKind,
        right: &silver::ExpKind,
    ) -> Result<vmir::Value, TcErr<TcType>> {
        let l = self.translate_exp_kind(left)?;
        let r = self.translate_exp_kind(right)?;

        let l_key = self.backend.tc_mut().get_var_key(&l);
        let r_key = self.backend.tc_mut().get_var_key(&r);

        let val = match op {
            silver::BinOp::And => {
                let false_ = vmir::Literal::Bool(false).into();
                self.backend
                    .emit_pure_inst(vmir::PureInst::Ternary(l, r, false_))
            }
            silver::BinOp::Or => {
                let true_ = vmir::Literal::Bool(true).into();
                self.backend
                    .emit_pure_inst(vmir::PureInst::Ternary(l, true_, r))
            }
            silver::BinOp::Implies => {
                let true_ = vmir::Literal::Bool(true).into();
                self.backend
                    .emit_pure_inst(vmir::PureInst::Ternary(l, r, true_))
            }
            silver::BinOp::Iff => {
                let not_r = self
                    .backend
                    .emit_pure_inst(vmir::PureInst::Unary(vmir::UnOp::Not, r.clone()));
                self.backend
                    .emit_pure_inst(vmir::PureInst::Ternary(l, r, not_r))
            }
            silver::BinOp::Eq => {
                self.backend
                    .emit_pure_inst(vmir::PureInst::Binary(vmir::BinOp::Eq, l, r))
            }
            silver::BinOp::Neq => {
                let l_eq_r =
                    self.backend
                        .emit_pure_inst(vmir::PureInst::Binary(vmir::BinOp::Eq, l, r));
                self.backend
                    .emit_pure_inst(vmir::PureInst::Unary(vmir::UnOp::Not, l_eq_r))
            }
            silver::BinOp::Lt => {
                self.backend
                    .emit_pure_inst(vmir::PureInst::Binary(vmir::BinOp::Lt, l, r))
            }
            silver::BinOp::Le => {
                let r_lt_l =
                    self.backend
                        .emit_pure_inst(vmir::PureInst::Binary(vmir::BinOp::Lt, r, l));
                self.backend
                    .emit_pure_inst(vmir::PureInst::Unary(vmir::UnOp::Not, r_lt_l))
            }
            silver::BinOp::Gt => {
                self.backend
                    .emit_pure_inst(vmir::PureInst::Binary(vmir::BinOp::Lt, r, l))
            }
            silver::BinOp::Ge => {
                let l_lt_r =
                    self.backend
                        .emit_pure_inst(vmir::PureInst::Binary(vmir::BinOp::Lt, l, r));
                self.backend
                    .emit_pure_inst(vmir::PureInst::Unary(vmir::UnOp::Not, l_lt_r))
            }
            silver::BinOp::Plus => {
                self.backend
                    .emit_pure_inst(vmir::PureInst::Binary(vmir::BinOp::Plus, l, r))
            }
            silver::BinOp::Minus => {
                self.backend
                    .emit_pure_inst(vmir::PureInst::Binary(vmir::BinOp::Minus, l, r))
            }
            silver::BinOp::Mult => {
                self.backend
                    .emit_pure_inst(vmir::PureInst::Binary(vmir::BinOp::Mult, l, r))
            }
            silver::BinOp::Div => {
                self.backend
                    .emit_pure_inst(vmir::PureInst::Binary(vmir::BinOp::Div, l, r))
            }
            _ => unimplemented!(),
        };
        let v_key = self.backend.tc_mut().get_var_key(&val);
        match op {
            silver::BinOp::And
            | silver::BinOp::Or
            | silver::BinOp::Implies
            | silver::BinOp::Iff => {
                self.backend
                    .tc_mut()
                    .impose(l_key.concretizes_explicit(TcType::Bool))?;
                self.backend
                    .tc_mut()
                    .impose(r_key.concretizes_explicit(TcType::Bool))?;
                self.backend
                    .tc_mut()
                    .impose(v_key.concretizes_explicit(TcType::Bool))?;
            }
            silver::BinOp::Eq | silver::BinOp::Neq => {
                self.backend.tc_mut().impose(l_key.equate_with(r_key))?;
                self.backend
                    .tc_mut()
                    .impose(v_key.concretizes_explicit(TcType::Bool))?;
            }
            silver::BinOp::Lt | silver::BinOp::Le | silver::BinOp::Gt | silver::BinOp::Ge => {
                self.backend
                    .tc_mut()
                    .impose(l_key.concretizes_explicit(TcType::Numeric))?;
                self.backend
                    .tc_mut()
                    .impose(r_key.concretizes_explicit(TcType::Numeric))?;
                self.backend.tc_mut().impose(l_key.equate_with(r_key))?;
                self.backend
                    .tc_mut()
                    .impose(v_key.concretizes_explicit(TcType::Bool))?;
            }
            silver::BinOp::Plus | silver::BinOp::Minus => {
                self.backend
                    .tc_mut()
                    .impose(l_key.concretizes_explicit(TcType::Numeric))?;
                self.backend
                    .tc_mut()
                    .impose(r_key.concretizes_explicit(TcType::Numeric))?;
                self.backend
                    .tc_mut()
                    .impose(v_key.is_sym_meet_of(l_key, r_key))?;
            }
            silver::BinOp::Mult | silver::BinOp::Div => {
                self.backend
                    .tc_mut()
                    .impose(l_key.concretizes_explicit(TcType::Numeric))?;
                self.backend
                    .tc_mut()
                    .impose(r_key.concretizes_explicit(TcType::Numeric))?;
                self.backend
                    .tc_mut()
                    .impose(v_key.concretizes_explicit(TcType::Numeric))?;
            }
            _ => unimplemented!(),
        }
        Ok(val)
    }

    fn translate_unop(
        &mut self,
        op: &silver::UnOp,
        exp: &silver::ExpKind,
    ) -> Result<vmir::Value, TcErr<TcType>> {
        let e = self.translate_exp_kind(exp)?;
        let e_key = self.backend.tc_mut().get_var_key(&e);
        let val = match op {
            silver::UnOp::Not => self
                .backend
                .emit_pure_inst(vmir::PureInst::Unary(vmir::UnOp::Not, e)),
            silver::UnOp::Neg => self
                .backend
                .emit_pure_inst(vmir::PureInst::Unary(vmir::UnOp::Neg, e)),
            silver::UnOp::Perm => {
                let heap = self.backend.current_heap();
                self.backend
                    .emit_pure_inst(vmir::PureInst::Heap(vmir::HeapDepInst {
                        heap,
                        kind: vmir::HeapDepInstKind::Perm(e),
                    }))
            }
            _ => unimplemented!("Unsupported unary operator: {:?}", op),
        };
        let v_key = self.backend.tc_mut().get_var_key(&val);
        match op {
            silver::UnOp::Not => {
                self.backend
                    .tc_mut()
                    .impose(e_key.concretizes_explicit(TcType::Bool))?;
                self.backend
                    .tc_mut()
                    .impose(v_key.concretizes_explicit(TcType::Bool))?;
            }
            silver::UnOp::Neg => {
                self.backend
                    .tc_mut()
                    .impose(e_key.concretizes_explicit(TcType::Numeric))?;
                self.backend
                    .tc_mut()
                    .impose(v_key.concretizes_explicit(TcType::Numeric))?;
                self.backend.tc_mut().impose(e_key.equate_with(v_key))?;
            }
            silver::UnOp::Perm => {
                self.backend
                    .tc_mut()
                    .impose(e_key.concretizes_explicit(TcType::Addr))?;
                self.backend
                    .tc_mut()
                    .impose(v_key.concretizes_explicit(TcType::Real))?;
            }
            _ => unimplemented!(),
        }
        Ok(val)
    }
}
