use nonmax::NonMaxU32;
use rusttyc::{TcErr, TcKey, TcVar, TypeChecker};

use crate::{
    silver,
    translate::{
        name_resolution::DeclKind,
        typecheck::{self, TcType},
        VmirTranslator,
    },
    vmir, HashMap,
};

impl TcVar for vmir::exp::Value {}

/// Context for translating expressions within a function/method
/// This tracks locals, generates SSA instructions, and accumulates type information
#[derive(Debug, Clone)]
pub struct ExpTranslationContext<'a, 'b> {
    /// Maps Silver variable names to VMIR local index and type
    env: HashMap<&'b str, (NonMaxU32, vmir::Type)>,
    /// Current instruction list being built
    insts: Vec<vmir::exp::InstKind>,

    tc: TypeChecker<typecheck::TcType, vmir::exp::Value>,
    /// Collected impure access expressions (acc(...))
    impures: Vec<vmir::exp::Acc>,
    /// Reference to the translator for looking up global names
    translator: &'a VmirTranslator,
}

impl<'a, 'b> ExpTranslationContext<'a, 'b> {
    pub fn new(translator: &'a VmirTranslator) -> Self {
        Self {
            env: HashMap::new(),
            insts: Vec::new(),
            tc: TypeChecker::new(),
            impures: Vec::new(),
            translator,
        }
    }

    pub fn translate_exp(
        mut self,
        exp: &silver::ExpKind,
        env: impl IntoIterator<Item = (&'b silver::IdnDecl, vmir::Type)>,
        ty: &vmir::Type,
    ) -> vmir::exp::Exp {
        for (idx, (name, ty)) in env.into_iter().enumerate() {
            let idx = NonMaxU32::new(idx as u32).expect("Too many parameters");
            self.env.insert(name.0 .0.as_str(), (idx, ty.into()));
        }

        let res = self.translate_exp_inner(exp).unwrap();

        let key = self.tc.get_var_key(&res);
        self.tc.impose(key.concretizes_explicit(ty.into())).unwrap();

        // Remember the keys of temporaries before we typecheck
        let inst_key: Vec<_> = self
            .insts
            .into_iter()
            .enumerate()
            .map(|(i, inst)| {
                let temp = vmir::exp::Temp::from(i).into();
                let key = self.tc.get_var_key(&temp);
                (inst, key)
            })
            .collect();

        let type_table = self.tc.type_check().unwrap_or_else(|e| {
            panic!("Type checking failed: {:?}", e);
        });

        // Convert instructions, resolving types using stored keys
        let insts = inst_key
            .into_iter()
            .map(|(kind, key)| vmir::exp::Inst {
                kind,
                ty: type_table[&key].clone(),
            })
            .collect();

        vmir::exp::Exp {
            insts,
            res,
            impures: self.impures,
        }
    }

    /// Add an instruction and return the temporary holding its result
    fn add_inst(&mut self, kind: vmir::exp::InstKind) -> vmir::exp::Value {
        let temp: vmir::exp::Temp = self.insts.len().into();
        self.insts.push(kind);
        temp.into()
    }

    fn translate_binop(
        &mut self,
        op: &silver::BinOp,
        left: &silver::ExpKind,
        right: &silver::ExpKind,
    ) -> Result<vmir::exp::Value, TcErr<TcType>> {
        let l = self.translate_exp_inner(left)?;
        let r = self.translate_exp_inner(right)?;

        let l_key = self.tc.get_var_key(&l);
        let r_key = self.tc.get_var_key(&r);

        // Desugar logical operators into ternaries
        let val = match op {
            silver::BinOp::And => {
                // l && r  =>  l ? r : false
                let false_ = vmir::exp::Literal::Bool(false).into();
                self.add_inst(vmir::exp::InstKind::Ternary(l, r, false_))
            }
            silver::BinOp::Or => {
                // l || r  =>  l ? true : r
                let true_ = vmir::exp::Literal::Bool(true).into();
                self.add_inst(vmir::exp::InstKind::Ternary(l, true_, r))
            }
            silver::BinOp::Implies => {
                // l ==> r  =>  l ? r : true
                let true_ = vmir::exp::Literal::Bool(true).into();
                self.add_inst(vmir::exp::InstKind::Ternary(l, r, true_))
            }
            silver::BinOp::Iff => {
                // l <==> r  =>  l ? r : !r
                let not_r =
                    self.add_inst(vmir::exp::InstKind::Unary(vmir::exp::UnOp::Not, r.clone()));
                self.add_inst(vmir::exp::InstKind::Ternary(l, r, not_r))
            }
            silver::BinOp::Eq => {
                self.add_inst(vmir::exp::InstKind::Binary(vmir::exp::BinOp::Eq, l, r))
            }
            silver::BinOp::Neq => {
                // l != r => !(l == r)
                let l_eq_r = self.add_inst(vmir::exp::InstKind::Binary(vmir::exp::BinOp::Eq, l, r));
                self.add_inst(vmir::exp::InstKind::Unary(vmir::exp::UnOp::Not, l_eq_r))
            }
            silver::BinOp::Lt => {
                self.add_inst(vmir::exp::InstKind::Binary(vmir::exp::BinOp::Lt, l, r))
            }
            silver::BinOp::Le => {
                // l <= r => !(r < l)
                let r_lt_l = self.add_inst(vmir::exp::InstKind::Binary(vmir::exp::BinOp::Lt, r, l));
                self.add_inst(vmir::exp::InstKind::Unary(vmir::exp::UnOp::Not, r_lt_l))
            }
            silver::BinOp::Gt => {
                // l > r => r < l
                self.add_inst(vmir::exp::InstKind::Binary(vmir::exp::BinOp::Lt, r, l))
            }
            silver::BinOp::Ge => {
                // l >= r => !(l < r)
                let l_lt_r = self.add_inst(vmir::exp::InstKind::Binary(vmir::exp::BinOp::Lt, l, r));
                self.add_inst(vmir::exp::InstKind::Unary(vmir::exp::UnOp::Not, l_lt_r))
            }
            silver::BinOp::Plus => {
                self.add_inst(vmir::exp::InstKind::Binary(vmir::exp::BinOp::Plus, l, r))
            }
            silver::BinOp::Minus => {
                self.add_inst(vmir::exp::InstKind::Binary(vmir::exp::BinOp::Minus, l, r))
            }
            silver::BinOp::Mult => {
                self.add_inst(vmir::exp::InstKind::Binary(vmir::exp::BinOp::Mult, l, r))
            }
            silver::BinOp::Div => {
                self.add_inst(vmir::exp::InstKind::Binary(vmir::exp::BinOp::Div, l, r))
            }
            _ => unimplemented!(),
        };
        let v_key = self.tc.get_var_key(&val);
        match op {
            silver::BinOp::And
            | silver::BinOp::Or
            | silver::BinOp::Implies
            | silver::BinOp::Iff => {
                self.tc.impose(l_key.concretizes_explicit(TcType::Bool))?;
                self.tc.impose(r_key.concretizes_explicit(TcType::Bool))?;
                self.tc.impose(v_key.concretizes_explicit(TcType::Bool))?;
            }
            silver::BinOp::Eq | silver::BinOp::Neq => {
                self.tc.impose(l_key.equate_with(r_key))?;
                self.tc.impose(v_key.concretizes_explicit(TcType::Bool))?;
            }
            silver::BinOp::Lt | silver::BinOp::Le | silver::BinOp::Gt | silver::BinOp::Ge => {
                self.tc
                    .impose(l_key.concretizes_explicit(TcType::Numeric))?;
                self.tc
                    .impose(r_key.concretizes_explicit(TcType::Numeric))?;
                self.tc.impose(l_key.equate_with(r_key))?;
                self.tc.impose(v_key.concretizes_explicit(TcType::Bool))?;
            }
            silver::BinOp::Plus | silver::BinOp::Minus => {
                self.tc
                    .impose(l_key.concretizes_explicit(TcType::Numeric))?;
                self.tc
                    .impose(r_key.concretizes_explicit(TcType::Numeric))?;
                self.tc.impose(v_key.is_sym_meet_of(l_key, r_key))?;
            }
            silver::BinOp::Mult | silver::BinOp::Div => {
                self.tc
                    .impose(l_key.concretizes_explicit(TcType::Numeric))?;
                self.tc
                    .impose(r_key.concretizes_explicit(TcType::Numeric))?;
                self.tc
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
    ) -> Result<vmir::exp::Value, TcErr<TcType>> {
        let e = self.translate_exp_inner(exp)?;
        let e_key = self.tc.get_var_key(&e);
        let val = match op {
            silver::UnOp::Not => self.add_inst(vmir::exp::InstKind::Unary(vmir::exp::UnOp::Not, e)),
            silver::UnOp::Neg => self.add_inst(vmir::exp::InstKind::Unary(vmir::exp::UnOp::Neg, e)),
            _ => unimplemented!("Unsupported unary operator: {:?}", op),
        };
        let v_key = self.tc.get_var_key(&val);
        match op {
            silver::UnOp::Not => {
                self.tc.impose(e_key.concretizes_explicit(TcType::Bool))?;
                self.tc.impose(v_key.concretizes_explicit(TcType::Bool))?;
            }
            silver::UnOp::Neg => {
                self.tc
                    .impose(e_key.concretizes_explicit(TcType::Numeric))?;
                self.tc
                    .impose(v_key.concretizes_explicit(TcType::Numeric))?;
                self.tc.impose(e_key.equate_with(v_key))?;
            }
            _ => unimplemented!(),
        }
        Ok(val)
    }

    /// Translate a Silver expression to VMIR SSA form
    /// Returns the Value representing the result and the inferred type
    fn translate_exp_inner(
        &mut self,
        exp: &silver::ExpKind,
    ) -> Result<vmir::exp::Value, TcErr<TcType>> {
        use silver::ExpKind;

        match exp {
            ExpKind::Const(const_) => self.translate_const(const_),

            ExpKind::Ident(ident) => {
                // Look up in locals
                if let Some((local_idx, ty)) = self.env.get(ident.0.as_str()) {
                    let val = vmir::exp::Local(*local_idx).into();
                    let key = self.tc.get_var_key(&val);
                    self.tc.impose(key.concretizes_explicit(ty.into()))?;
                    Ok(val)
                } else {
                    panic!("Undefined variable: {}", ident.0);
                }
            }

            ExpKind::BinOp(op, left, right) => self.translate_binop(op, left, right),

            ExpKind::UnOp(op, e) => self.translate_unop(op, e),

            ExpKind::Ternary(cond, then, else_) => {
                let cond = self.translate_exp_inner(cond)?;
                let then = self.translate_exp_inner(then)?;
                let else_ = self.translate_exp_inner(else_)?;

                let cond_key = self.tc.get_var_key(&cond);
                let then_key = self.tc.get_var_key(&then);
                let else_key = self.tc.get_var_key(&else_);

                let val = self.add_inst(vmir::exp::InstKind::Ternary(cond, then, else_));
                let val_key = self.tc.get_var_key(&val);

                self.tc
                    .impose(cond_key.concretizes_explicit(TcType::Bool))?;
                self.tc.impose(val_key.is_sym_meet_of(then_key, else_key))?;
                Ok(val)
            }

            func_app @ ExpKind::FuncApp(func_name, args) => {
                // Need to check if we are dealing with a predicate call
                let func_id = self
                    .translator
                    .interner
                    .get(&func_name.0)
                    .expect(&format!("Function {} not found", func_name.0));

                let is_predicate = self
                    .translator
                    .name_kinds
                    .get(func_id)
                    .map(|kind| *kind == DeclKind::Predicate)
                    .unwrap_or(false);

                if is_predicate {
                    // Desugar predicate(args) into acc(predicate(args), write)
                    let acc_exp = silver::AccExp {
                        acc: silver::LocAccess {
                            loc: Box::new(func_app.clone()),
                        },
                        perm: Box::new(ExpKind::Const(silver::ConstKind::Real(
                            num::BigRational::from_integer(1.into()),
                        ))),
                    };

                    self.translate_acc_exp(&acc_exp)
                } else {
                    self.translate_func_app(func_name, args)
                }
            }

            ExpKind::Field(base, field_name) => {
                self.translate_func_app(field_name, &[base.clone()])
            }

            ExpKind::Acc(acc_exp) => self.translate_acc_exp(acc_exp),

            _ => unimplemented!("Expression translation: {:?}", exp),
        }
    }

    fn match_type(&mut self, ty: &vmir::Type, key: TcKey) -> Result<(), TcErr<TcType>> {
        self.tc.impose(key.concretizes_explicit(ty.into()))?;
        match ty {
            vmir::Type::Addr(inner) => {
                let child = self.tc.get_child_key(key, 0)?;
                self.match_type(inner, child)
            }
            _ => Ok(()),
        }
    }

    fn translate_func_app(
        &mut self,
        func_name: &silver::Ident,
        args: &[silver::Exp],
    ) -> Result<vmir::exp::Value, TcErr<TcType>> {
        let func_id = self
            .translator
            .interner
            .get(&func_name.0)
            .expect(&format!("Function {} not found", func_name.0));

        let args = args
            .iter()
            .map(|arg| self.translate_exp_inner(arg))
            .collect::<Result<Vec<_>, _>>()?;

        let sig = self.translator.signatures.function_sig(func_id);

        // Add type constraitns for arguments
        for (arg, ty) in args.iter().zip(sig.args.iter()) {
            let arg_key = self.tc.get_var_key(arg);
            self.match_type(ty, arg_key)?;
        }

        let val = self.add_inst(vmir::exp::InstKind::Call(func_id, args));

        // Add type constraint for return type
        let val_key = self.tc.get_var_key(&val);
        self.match_type(&sig.ret, val_key)?;

        Ok(val)
    }

    fn translate_loc_exp(
        &mut self,
        loc_exp: &silver::LocAccess,
    ) -> Result<vmir::exp::Value, TcErr<TcType>> {
        match loc_exp.loc.as_ref() {
            silver::ExpKind::FuncApp(func_name, args) => self.translate_func_app(func_name, args),
            silver::ExpKind::Field(..) => self.translate_exp_inner(&loc_exp.loc),
            _ => unreachable!(),
        }
    }

    fn translate_acc_exp(
        &mut self,
        acc_exp: &silver::AccExp,
    ) -> Result<vmir::exp::Value, TcErr<TcType>> {
        let loc_val = self.translate_loc_exp(&acc_exp.acc)?;
        let loc_key = self.tc.get_var_key(&loc_val);
        self.tc
            .impose(loc_key.concretizes_explicit(typecheck::TcType::Addr))?;

        let perm_val = self.translate_exp_inner(&acc_exp.perm)?;
        let perm_key = self.tc.get_var_key(&perm_val);
        self.tc
            .impose(perm_key.concretizes_explicit(typecheck::TcType::Real))?;

        // Add to impures list
        self.impures.push(vmir::exp::Acc {
            loc: loc_val.clone(),
            perm: perm_val,
        });

        // acc() expressions evaluate to true (unit/bool) in the pure context
        Ok(vmir::exp::Literal::Bool(true).into())
    }

    fn translate_const(
        &mut self,
        const_: &silver::ConstKind,
    ) -> Result<vmir::exp::Value, TcErr<TcType>> {
        let val = match const_ {
            silver::ConstKind::Bool(b) => vmir::exp::Literal::Bool(*b),
            silver::ConstKind::Int(i) => vmir::exp::Literal::Int(i.clone()),
            silver::ConstKind::Real(r) => vmir::exp::Literal::Real(r.clone()),
            silver::ConstKind::Null => vmir::exp::Literal::Null,
            _ => unimplemented!("Unsupported constant: {:?}", const_),
        }
        .into();
        let ty = &match const_ {
            silver::ConstKind::Bool(_) => vmir::Type::Bool,
            silver::ConstKind::Int(_) => vmir::Type::Int,
            silver::ConstKind::Real(_) => vmir::Type::Real,
            silver::ConstKind::Null => vmir::Type::Ref,
            _ => unimplemented!(),
        };
        let key = self.tc.get_var_key(&val);
        self.tc.impose(key.concretizes_explicit(ty.into()))?;
        Ok(val)
    }
}
