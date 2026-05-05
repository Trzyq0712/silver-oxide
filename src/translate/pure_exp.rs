use rusttyc::{TcErr, TcKey};

use crate::{
    silver,
    translate::{typecheck::TcType, VmirTc, VmirTranslator},
    vmir,
};

pub trait PureExpBackend {
    /// The current symbolic value of a variable.
    fn resolve_var(&self, ident: &silver::Ident) -> Result<vmir::Val, ()>;

    fn old_heap(&self, label: Option<&silver::Ident>) -> Result<vmir::HeapVal, ()>;

    /// Emit a pure instruction, in return get back the register it
    /// was saved to.
    fn emit_pure(&mut self, pure: vmir::PureInst) -> vmir::Val;

    /// Emit an assertion.
    fn emit_assert(&mut self, check: vmir::Val);

    /// Access to the typchecker for asserting type information
    fn tc_mut(&mut self) -> &mut VmirTc;

    /// Resolve the name of a global identifier.
    fn resolve_name(&self, ident: &silver::Ident) -> Result<vmir::MemberId, ()>;
}

pub struct PureExpTranslator<'a, B: PureExpBackend> {
    pub backend: &'a mut B,
    /// The path condtition under which the current expression is being translated.
    /// This is used for path-sensitive reasoning, i.e. emitting assertions.
    /// An empty path condition is equivalent to `true`.
    pub pc: Option<vmir::Val>,
    pub heap: vmir::HeapVal,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Polarity {
    Positive,
    Negative,
}

impl<'a, B: PureExpBackend> PureExpTranslator<'a, B> {
    pub fn translate(&mut self, exp: &silver::PureExp) -> Result<vmir::Val, TcErr<TcType>> {
        self.translate_exp_kind(exp.as_ref())
    }

    fn translate_exp_kind(&mut self, exp: &silver::ExpKind) -> Result<vmir::Val, TcErr<TcType>> {
        use silver::ExpKind;
        match exp {
            ExpKind::Const(const_) => self.translate_const(const_),
            ExpKind::Ident(ident) => Ok(self.backend.resolve_var(ident).unwrap()),
            ExpKind::Old(label, exp) => {
                let old_heap = self.backend.old_heap(label.as_ref()).unwrap();
                self.with_heap(old_heap, |s| s.translate_exp_kind(exp))
            }
            ExpKind::BinOp(op, left, right) => self.translate_binop(op, left, right),
            ExpKind::UnOp(op, e) => self.translate_unop(op, e),
            ExpKind::Ternary(cond, then, else_) => {
                let cond = self.translate_exp_kind(cond)?;
                let then = self.with_pc(cond.clone(), Polarity::Positive, |s| {
                    s.translate_exp_kind(then)
                })?;
                let else_ = self.with_pc(cond.clone(), Polarity::Negative, |s| {
                    s.translate_exp_kind(else_)
                })?;

                let cond_key = self.backend.tc_mut().get_var_key(&cond);
                let then_key = self.backend.tc_mut().get_var_key(&then);
                let else_key = self.backend.tc_mut().get_var_key(&else_);

                let val = self
                    .backend
                    .emit_pure(vmir::PureInst::Ternary(cond, then, else_));
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

    fn with_heap<R>(&mut self, heap: vmir::HeapVal, f: impl FnOnce(&mut Self) -> R) -> R {
        let prev = self.heap.clone();
        self.heap = heap;
        let res = f(self);
        self.heap = prev;
        res
    }

    fn with_pc<R>(
        &mut self,
        cond: vmir::Val,
        polarity: Polarity,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let curr_pc = self.pc.as_ref().unwrap_or(&vmir::TRUE);
        let new_pc = self.backend.emit_pure(match polarity {
            Polarity::Positive => vmir::PureInst::Ternary(cond, curr_pc.clone(), vmir::FALSE),
            Polarity::Negative => vmir::PureInst::Ternary(cond, vmir::FALSE, curr_pc.clone()),
        });
        let saved_pc = self.pc.replace(new_pc);
        let res = f(self);
        self.pc = saved_pc;
        res
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

    fn translate_const(&mut self, const_: &silver::ConstKind) -> Result<vmir::Val, TcErr<TcType>> {
        let val = vmir::Val::Literal(match const_ {
            silver::ConstKind::Bool(b) => vmir::Literal::Bool(*b),
            silver::ConstKind::Int(i) => vmir::Literal::Int(i.clone()),
            silver::ConstKind::Real(r) => vmir::Literal::Real(r.clone()),
            silver::ConstKind::Null => vmir::Literal::Null,
            _ => unimplemented!("Unsupported constant: {:?}", const_),
        });
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

    fn assert(&mut self, cond: vmir::Val) {
        let check = if let Some(pc) = &self.pc {
            self.backend
                .emit_pure(vmir::PureInst::Ternary(pc.clone(), cond, vmir::TRUE))
        } else {
            cond
        };

        self.backend.emit_assert(check);
    }

    fn translate_field_access(
        &mut self,
        base: &silver::Exp,
        field: &silver::Ident,
    ) -> Result<vmir::Val, TcErr<TcType>> {
        // 1. Emit a function call to the field-function to get the memory address
        let addr = self.translate_func_app(field, &[base.clone()])?;
        // 2. Assert that permission is positive under the current pc
        let perm = self
            .backend
            .emit_pure(vmir::PureInst::Perm(self.heap.clone(), addr.clone()));
        let positive =
            self.backend
                .emit_pure(vmir::PureInst::Binary(vmir::BinOp::Lt, vmir::none(), perm));
        self.assert(positive);
        // 3. Perform a dereference
        let val = self
            .backend
            .emit_pure(vmir::PureInst::Deref(self.heap.clone(), addr));

        Ok(val)
    }

    fn translate_func_app(
        &mut self,
        func_name: &silver::Ident,
        args: &[silver::Exp],
    ) -> Result<vmir::Val, TcErr<TcType>> {
        let func_id = self.backend.resolve_name(func_name).unwrap();

        let args = args
            .iter()
            .map(|arg| self.translate_exp_kind(arg))
            .collect::<Result<Vec<_>, _>>()?;

        // let sig = self
        //     .backend
        //     .translator()
        //     .signatures()
        //     .function_sig(func_id)
        //     .clone();

        // for (arg, ty) in args.iter().zip(sig.args.iter()) {
        //     let arg_key = self.backend.tc_mut().get_var_key(arg);
        //     self.match_type(ty, arg_key)?;
        // }

        let func_call = vmir::FunctionCall {
            func_id,
            args,
            heap_ctx: self.heap.clone(),
        };
        let val = self
            .backend
            .emit_pure(vmir::PureInst::FunctionCall(func_call));
        // let val_key = self.backend.tc_mut().get_var_key(&val);
        // self.match_type(&sig.ret, val_key)?;
        Ok(val)
    }

    fn translate_binop(
        &mut self,
        op: &silver::BinOp,
        left: &silver::ExpKind,
        right: &silver::ExpKind,
    ) -> Result<vmir::Val, TcErr<TcType>> {
        let l = self.translate_exp_kind(left)?;
        let r = self.translate_exp_kind(right)?;

        let l_key = self.backend.tc_mut().get_var_key(&l);
        let r_key = self.backend.tc_mut().get_var_key(&r);

        let val = match op {
            silver::BinOp::And => {
                self.backend
                    .emit_pure(vmir::PureInst::Ternary(l, r, vmir::FALSE))
            }
            silver::BinOp::Or => self
                .backend
                .emit_pure(vmir::PureInst::Ternary(l, vmir::TRUE, r)),
            silver::BinOp::Implies => {
                self.backend
                    .emit_pure(vmir::PureInst::Ternary(l, r, vmir::TRUE))
            }
            silver::BinOp::Eq | silver::BinOp::Iff => self
                .backend
                .emit_pure(vmir::PureInst::Binary(vmir::BinOp::Eq, l, r)),
            silver::BinOp::Neq => {
                let l_eq_r = self
                    .backend
                    .emit_pure(vmir::PureInst::Binary(vmir::BinOp::Eq, l, r));
                self.backend
                    .emit_pure(vmir::PureInst::Unary(vmir::UnOp::Not, l_eq_r))
            }
            silver::BinOp::Lt => {
                self.backend
                    .emit_pure(vmir::PureInst::Binary(vmir::BinOp::Lt, l, r))
            }
            silver::BinOp::Le => {
                let r_lt_l = self
                    .backend
                    .emit_pure(vmir::PureInst::Binary(vmir::BinOp::Lt, r, l));
                self.backend
                    .emit_pure(vmir::PureInst::Unary(vmir::UnOp::Not, r_lt_l))
            }
            silver::BinOp::Gt => {
                self.backend
                    .emit_pure(vmir::PureInst::Binary(vmir::BinOp::Lt, r, l))
            }
            silver::BinOp::Ge => {
                let l_lt_r = self
                    .backend
                    .emit_pure(vmir::PureInst::Binary(vmir::BinOp::Lt, l, r));
                self.backend
                    .emit_pure(vmir::PureInst::Unary(vmir::UnOp::Not, l_lt_r))
            }
            silver::BinOp::Plus => {
                self.backend
                    .emit_pure(vmir::PureInst::Binary(vmir::BinOp::Plus, l, r))
            }
            silver::BinOp::Minus => {
                self.backend
                    .emit_pure(vmir::PureInst::Binary(vmir::BinOp::Minus, l, r))
            }
            silver::BinOp::Mult => {
                self.backend
                    .emit_pure(vmir::PureInst::Binary(vmir::BinOp::Mult, l, r))
            }
            silver::BinOp::Div => {
                let denom_zero = self.backend.emit_pure(vmir::PureInst::Binary(
                    vmir::BinOp::Eq,
                    r.clone(),
                    vmir::none(),
                ));
                let denom_nonzero = self
                    .backend
                    .emit_pure(vmir::PureInst::Unary(vmir::UnOp::Not, denom_zero));
                self.assert(denom_nonzero);
                self.backend
                    .emit_pure(vmir::PureInst::Binary(vmir::BinOp::Div, l, r))
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
    ) -> Result<vmir::Val, TcErr<TcType>> {
        let e = self.translate_exp_kind(exp)?;
        let e_key = self.backend.tc_mut().get_var_key(&e);
        let val = match op {
            silver::UnOp::Not => self
                .backend
                .emit_pure(vmir::PureInst::Unary(vmir::UnOp::Not, e)),
            silver::UnOp::Neg => self
                .backend
                .emit_pure(vmir::PureInst::Unary(vmir::UnOp::Neg, e)),
            silver::UnOp::Perm => self
                .backend
                .emit_pure(vmir::PureInst::Perm(self.heap.clone(), e)),
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
