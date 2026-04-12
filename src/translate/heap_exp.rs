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

impl TcVar for vmir::Value {}

enum Polarity {
    Positive,
    Negative,
}

enum PathCond {
    None,
    Cond(Polarity, vmir::Value),
}

/// Context for translating expressions within a function/method
/// This tracks locals, generates SSA instructions, and accumulates type information
#[derive(Debug, Clone)]
pub struct HeapExpTranslCtxt<'a, 'b> {
    /// Argument types for the heap expression, these correspond to the expressions [e0, ..., en],
    /// where n = len(args) - 1
    args: Vec<vmir::Type>,
    /// Current instruction list being built
    insts: Vec<vmir::InstKind>,

    tc: TypeChecker<typecheck::TcType, vmir::Value>,

    /// On-path condition used for building path-sensitive `acc` expressions
    /// For example, `b ==> acc(x.f, 1/1)` would have a path condition of `b` when translating the
    /// `acc` expression
    path_cond: Option<vmir::Value>,

    /// Current state of the heap, initially mapped to one of the heaps from the input
    heap: vmir::Value,
    /// The old heap value for ensures clauses with `old` expressions
    old_heap: Option<vmir::Value>,

    /// Maps a named Silver local to a vmir temporary in the `args`
    locals: HashMap<&'b silver::Ident, vmir::Temp>,

    /// Reference to the translator for looking up global names
    translator: &'a VmirTranslator,
}

impl<'a, 'b> HeapExpTranslCtxt<'a, 'b> {
    pub fn new_for_requires(
        translator: &'a VmirTranslator,
        method: vmir::MemberId,
        args: impl IntoIterator<Item = &'b silver::IdnDecl>,
    ) -> Self {
        let exp_args = [
            &[vmir::Type::Heap].as_slice(), // the input heap
            translator.signatures.method_sig(method).args.as_slice(),
        ]
        .concat();

        let heap = vmir::Value::Temp(0); // 0-th arg is the starting heap

        let mut tc = TypeChecker::new();
        for (idx, ty) in exp_args.iter().enumerate() {
            let key = tc.get_var_key(&vmir::Value::Temp(idx));
            tc.impose(key.concretizes_explicit(ty.into())).unwrap();
        }

        let locals: HashMap<&'b silver::Ident, vmir::Temp> = args
            .into_iter()
            .enumerate()
            .map(|(idx, decl)| (&decl.0, idx + 1)) // skip the 0-th arg which is the heap
            .collect();

        Self {
            args: exp_args,
            insts: Vec::new(),
            tc,
            path_cond: None,
            heap,
            old_heap: None,
            locals,
            translator,
        }
    }

    pub fn new_for_ensures(
        translator: &'a VmirTranslator,
        method: vmir::MemberId,
        args: impl IntoIterator<Item = &'b silver::IdnDecl>,
        rets: impl IntoIterator<Item = &'b silver::IdnDecl>,
    ) -> Self {
        let exp_args = [
            &[vmir::Type::Heap, vmir::Type::Heap].as_slice(), // the input heap and old heap
            translator.signatures.method_sig(method).args.as_slice(),
            translator.signatures.method_sig(method).ret.as_slice(),
        ]
        .concat();

        let heap = vmir::Value::Temp(0); // 0-th arg is the starting heap
        let old_heap = vmir::Value::Temp(1); // 1-st arg is the old heap

        let mut tc = TypeChecker::new();
        for (idx, ty) in exp_args.iter().enumerate() {
            let key = tc.get_var_key(&vmir::Value::Temp(idx));
            tc.impose(key.concretizes_explicit(ty.into())).unwrap();
        }

        let locals: HashMap<&'b silver::Ident, vmir::Temp> = std::iter::chain(args, rets)
            .enumerate()
            .map(|(idx, decl)| (&decl.0, idx + 2)) // skip the first 2 args which are the heaps
            .collect();

        Self {
            args: exp_args,
            insts: Vec::new(),
            tc,
            path_cond: None,
            heap,
            old_heap: Some(old_heap),
            locals,
            translator,
        }
    }

    // pub fn new(
    //     translator: &'a VmirTranslator,
    //     locals: impl IntoIterator<Item = (&'b silver::IdnDecl, vmir::Type)>,
    // ) -> Self {
    //     let env: HashMap<&'b str, (NonMaxU32, vmir::Type)> = locals
    //         .into_iter()
    //         .enumerate()
    //         .map(|(idx, (name, ty))| {
    //             let idx = NonMaxU32::new(idx as u32).expect("Too many parameters");
    //             (name.0 .0.as_str(), (idx, ty.into()))
    //         })
    //         .collect();
    //
    //     Self::with_env(translator, env)
    // }

    // pub fn with_env(
    //     translator: &'a VmirTranslator,
    //     env: HashMap<&'b str, (NonMaxU32, vmir::Type)>,
    // ) -> Self {
    //     Self {
    //         env,
    //         insts: Vec::new(),
    //         tc: TypeChecker::new(),
    //         heap: vmir::Literal::EmptyHeap.into(),
    //         translator,
    //     }
    // }

    pub fn translate_exp(mut self, exp: &silver::ExpKind) -> vmir::HeapExp {
        let res_pure = self.translate_exp_inner(exp).unwrap();

        let key = self.tc.get_var_key(&res_pure);
        self.tc
            .impose(key.concretizes_explicit(TcType::Bool))
            .unwrap();

        // Remember the keys of temporaries before we typecheck
        let inst_key: Vec<_> = self
            .insts
            .into_iter()
            .enumerate()
            .map(|(i, inst)| {
                let temp = vmir::Value::Temp(i);
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
            .map(|(kind, key)| vmir::Inst {
                kind,
                ty: type_table[&key].clone(),
            })
            .collect();

        vmir::HeapExp {
            input_types: self.args,
            insts,
            res_pure,
            res_impure: self.heap,
        }
    }

    /// Add an instruction and return the temporary holding its result
    fn add_inst(&mut self, kind: vmir::InstKind) -> vmir::Value {
        let temp = self.insts.len() + self.args.len();
        self.insts.push(kind);
        vmir::Value::Temp(temp)
    }

    fn add_heap_inst<F>(&mut self, f: F)
    where
        F: FnOnce(vmir::Value) -> vmir::InstKind,
    {
        let prev_heap = self.heap.clone();
        let val = self.add_inst(f(prev_heap));
        let key = self.tc.get_var_key(&val);
        self.tc
            .impose(key.concretizes_explicit(TcType::Heap))
            .unwrap();
        self.heap = val;
    }

    fn translate_binop(
        &mut self,
        op: &silver::BinOp,
        left: &silver::ExpKind,
        right: &silver::ExpKind,
    ) -> Result<vmir::Value, TcErr<TcType>> {
        let l = self.translate_exp_inner(left)?;
        let r = self.translate_exp_inner(right)?;

        let l_key = self.tc.get_var_key(&l);
        let r_key = self.tc.get_var_key(&r);

        // Desugar logical operators into ternaries
        let val = match op {
            silver::BinOp::And => {
                // l && r  =>  l ? r : false
                let false_ = vmir::Literal::Bool(false).into();
                self.add_inst(vmir::InstKind::Ternary(l, r, false_))
            }
            silver::BinOp::Or => {
                // l || r  =>  l ? true : r
                let true_ = vmir::Literal::Bool(true).into();
                self.add_inst(vmir::InstKind::Ternary(l, true_, r))
            }
            silver::BinOp::Implies => {
                // l ==> r  =>  l ? r : true
                let true_ = vmir::Literal::Bool(true).into();
                self.add_inst(vmir::InstKind::Ternary(l, r, true_))
            }
            silver::BinOp::Iff => {
                // l <==> r  =>  l ? r : !r
                let not_r = self.add_inst(vmir::InstKind::Unary(vmir::UnOp::Not, r.clone()));
                self.add_inst(vmir::InstKind::Ternary(l, r, not_r))
            }
            silver::BinOp::Eq => self.add_inst(vmir::InstKind::Binary(vmir::BinOp::Eq, l, r)),
            silver::BinOp::Neq => {
                // l != r => !(l == r)
                let l_eq_r = self.add_inst(vmir::InstKind::Binary(vmir::BinOp::Eq, l, r));
                self.add_inst(vmir::InstKind::Unary(vmir::UnOp::Not, l_eq_r))
            }
            silver::BinOp::Lt => self.add_inst(vmir::InstKind::Binary(vmir::BinOp::Lt, l, r)),
            silver::BinOp::Le => {
                // l <= r => !(r < l)
                let r_lt_l = self.add_inst(vmir::InstKind::Binary(vmir::BinOp::Lt, r, l));
                self.add_inst(vmir::InstKind::Unary(vmir::UnOp::Not, r_lt_l))
            }
            silver::BinOp::Gt => {
                // l > r => r < l
                self.add_inst(vmir::InstKind::Binary(vmir::BinOp::Lt, r, l))
            }
            silver::BinOp::Ge => {
                // l >= r => !(l < r)
                let l_lt_r = self.add_inst(vmir::InstKind::Binary(vmir::BinOp::Lt, l, r));
                self.add_inst(vmir::InstKind::Unary(vmir::UnOp::Not, l_lt_r))
            }
            silver::BinOp::Plus => self.add_inst(vmir::InstKind::Binary(vmir::BinOp::Plus, l, r)),
            silver::BinOp::Minus => self.add_inst(vmir::InstKind::Binary(vmir::BinOp::Minus, l, r)),
            silver::BinOp::Mult => self.add_inst(vmir::InstKind::Binary(vmir::BinOp::Mult, l, r)),
            silver::BinOp::Div => self.add_inst(vmir::InstKind::Binary(vmir::BinOp::Div, l, r)),
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
    ) -> Result<vmir::Value, TcErr<TcType>> {
        let e = self.translate_exp_inner(exp)?;
        let e_key = self.tc.get_var_key(&e);
        let val = match op {
            silver::UnOp::Not => self.add_inst(vmir::InstKind::Unary(vmir::UnOp::Not, e)),
            silver::UnOp::Neg => self.add_inst(vmir::InstKind::Unary(vmir::UnOp::Neg, e)),
            silver::UnOp::Perm => self.add_inst(vmir::InstKind::Perm(self.heap.clone(), e)),
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
            silver::UnOp::Perm => {
                self.tc.impose(e_key.concretizes_explicit(TcType::Addr))?;
                self.tc.impose(v_key.concretizes_explicit(TcType::Real))?;
            }
            _ => unimplemented!(),
        }
        Ok(val)
    }

    fn translate_ident(&mut self, ident: &silver::Ident) -> vmir::Value {
        let Some(local_idx) = self.locals.get(ident) else {
            panic!("Undefined variable: {}", ident.0);
        };
        vmir::Value::Temp(*local_idx)
    }

    /// Translate a Silver expression to VMIR SSA form
    /// Returns the Value representing the result and the inferred type
    fn translate_exp_inner(&mut self, exp: &silver::ExpKind) -> Result<vmir::Value, TcErr<TcType>> {
        use silver::ExpKind;

        match exp {
            ExpKind::Const(const_) => self.translate_const(const_),

            ExpKind::Ident(ident) => Ok(self.translate_ident(ident)),

            ExpKind::BinOp(op, left, right) => self.translate_binop(op, left, right),

            ExpKind::UnOp(op, e) => self.translate_unop(op, e),

            ExpKind::Ternary(cond, then, else_) => {
                let cond = self.translate_exp_inner(cond)?;
                self.path_cond = Some(cond.clone());
                let then = self.translate_exp_inner(then)?;
                let else_ = self.translate_exp_inner(else_)?;

                let cond_key = self.tc.get_var_key(&cond);
                let then_key = self.tc.get_var_key(&then);
                let else_key = self.tc.get_var_key(&else_);

                let val = self.add_inst(vmir::InstKind::Ternary(cond, then, else_));
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
    ) -> Result<vmir::Value, TcErr<TcType>> {
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

        let val = self.add_inst(vmir::InstKind::Call(func_id, args));

        // Add type constraint for return type
        let val_key = self.tc.get_var_key(&val);
        self.match_type(&sig.ret, val_key)?;

        Ok(val)
    }

    fn translate_loc_exp(
        &mut self,
        loc_exp: &silver::LocAccess,
    ) -> Result<vmir::Value, TcErr<TcType>> {
        match loc_exp.loc.as_ref() {
            silver::ExpKind::FuncApp(func_name, args) => self.translate_func_app(func_name, args),
            silver::ExpKind::Field(..) => self.translate_exp_inner(&loc_exp.loc),
            _ => unreachable!(),
        }
    }

    fn translate_acc_exp(
        &mut self,
        acc_exp: &silver::AccExp,
    ) -> Result<vmir::Value, TcErr<TcType>> {
        let loc = self.translate_loc_exp(&acc_exp.acc)?;
        let loc_key = self.tc.get_var_key(&loc);
        self.tc.impose(loc_key.concretizes_explicit(TcType::Addr))?;

        let amt = self.translate_exp_inner(&acc_exp.perm)?;
        let amt_key = self.tc.get_var_key(&amt);
        self.tc.impose(amt_key.concretizes_explicit(TcType::Real))?;

        self.add_heap_inst(|curr_heap| vmir::InstKind::Acc(curr_heap, loc, amt));

        // acc() expressions evaluate to true (bool) in the pure context
        Ok(vmir::Literal::Bool(true).into())
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
