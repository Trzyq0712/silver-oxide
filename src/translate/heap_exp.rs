use rusttyc::{TcErr, TcKey, TcVar, TypeChecker};

use crate::{
    silver,
    translate::{
        pure_exp::{PureExpBackend, PureExpTranslator},
        typecheck::{self, TcType},
        VmirTranslator,
    },
    vmir::{self, AccInst},
    HashMap,
};

impl TcVar for vmir::Value {}

#[derive(Debug, Clone)]
enum Polarity {
    Positive,
    Negative,
}

#[derive(Debug, Clone)]
enum PathCond {
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
    insts: Vec<vmir::HeapInstKind>,

    tc: TypeChecker<typecheck::TcType, vmir::Value>,

    /// Stack of active path conditions used for path-sensitive `acc` translation.
    /// Nested conditionals push branch guards and pop on branch exit.
    path_cond_stack: Vec<PathCond>,

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
            path_cond_stack: Vec::new(),
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
            path_cond_stack: Vec::new(),
            heap,
            old_heap: Some(old_heap),
            locals,
            translator,
        }
    }

    pub fn translate_assert_exp(mut self, exp: &silver::HeapExp) -> vmir::HeapExp {
        let res_pure = self.translate_heap_exp_inner(exp).unwrap();

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
                let temp = vmir::Value::Temp(i + self.args.len());
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
            .map(|(kind, key)| vmir::HeapInst {
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

    fn translate_heap_exp_inner(
        &mut self,
        exp: &silver::HeapExp,
    ) -> Result<vmir::Value, TcErr<TcType>> {
        match &exp.kind {
            silver::HeapExpKind::Pure(exp) => PureExpTranslator::new(self).translate_exp_kind(exp),
            silver::HeapExpKind::Acc(acc) => self.translate_acc_exp(acc),
            silver::HeapExpKind::Conjunction(heap_exps) => {
                let mut pure = None;
                for heap_exp in heap_exps {
                    let next = self.translate_heap_exp_inner(heap_exp)?;
                    pure = Some(match pure {
                        None => next,
                        Some(prev) => self.translate_bool_and(prev, next)?,
                    });
                }
                Ok(pure.unwrap_or_else(|| vmir::Literal::Bool(true).into()))
            }
            silver::HeapExpKind::MagicWand(..) => unimplemented!("heap magic wand translation"),
            silver::HeapExpKind::Ternary(cond, then_heap, else_heap) => {
                let cond = PureExpTranslator::new(self).translate_exp_kind(cond)?;
                let then =
                    self.with_branch_path_cond(cond.clone(), Polarity::Positive, |this| {
                        this.translate_heap_exp_inner(then_heap)
                    })?;
                let else_ =
                    self.with_branch_path_cond(cond.clone(), Polarity::Negative, |this| {
                        this.translate_heap_exp_inner(else_heap)
                    })?;

                let cond_key = self.tc.get_var_key(&cond);
                let then_key = self.tc.get_var_key(&then);
                let else_key = self.tc.get_var_key(&else_);

                let val = self.add_inst(vmir::HeapInstKind::Pure(vmir::PureInst::Ternary(
                    cond, then, else_,
                )));
                let val_key = self.tc.get_var_key(&val);

                self.tc
                    .impose(cond_key.concretizes_explicit(TcType::Bool))?;
                self.tc.impose(val_key.is_sym_meet_of(then_key, else_key))?;
                Ok(val)
            }
        }
    }

    fn push_path_cond(&mut self, path_cond: PathCond) {
        self.path_cond_stack.push(path_cond);
    }

    fn pop_path_cond(&mut self) {
        self.path_cond_stack
            .pop()
            .expect("path condition stack underflow");
    }

    fn with_branch_path_cond<T>(
        &mut self,
        cond: vmir::Value,
        polarity: Polarity,
        f: impl FnOnce(&mut Self) -> Result<T, TcErr<TcType>>,
    ) -> Result<T, TcErr<TcType>> {
        self.push_path_cond(PathCond::Cond(polarity, cond));
        let res = f(self);
        self.pop_path_cond();
        res
    }

    /// Add an instruction and return the temporary holding its result
    fn add_inst(&mut self, kind: vmir::HeapInstKind) -> vmir::Value {
        let temp = self.insts.len() + self.args.len();
        self.insts.push(kind);
        vmir::Value::Temp(temp)
    }

    fn add_heap_inst<F>(&mut self, f: F)
    where
        F: FnOnce(vmir::Value) -> vmir::HeapInstKind,
    {
        let prev_heap = self.heap.clone();
        let val = self.add_inst(f(prev_heap));
        let key = self.tc.get_var_key(&val);
        self.tc
            .impose(key.concretizes_explicit(TcType::Heap))
            .unwrap();
        self.heap = val;
    }

    fn translate_bool_and(
        &mut self,
        left: vmir::Value,
        right: vmir::Value,
    ) -> Result<vmir::Value, TcErr<TcType>> {
        let left_key = self.tc.get_var_key(&left);
        let right_key = self.tc.get_var_key(&right);

        let false_ = vmir::Literal::Bool(false).into();
        let val = self.add_inst(vmir::HeapInstKind::Pure(vmir::PureInst::Ternary(
            left, right, false_,
        )));
        let val_key = self.tc.get_var_key(&val);

        self.tc
            .impose(left_key.concretizes_explicit(TcType::Bool))?;
        self.tc
            .impose(right_key.concretizes_explicit(TcType::Bool))?;
        self.tc.impose(val_key.concretizes_explicit(TcType::Bool))?;
        Ok(val)
    }

    /// Translate a Silver expression to VMIR SSA form
    /// Returns the Value representing the result and the inferred type
    fn translate_exp_inner(&mut self, exp: &silver::ExpKind) -> Result<vmir::Value, TcErr<TcType>> {
        PureExpTranslator::new(self).translate_exp_kind(exp)
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

        let val = self.add_inst(vmir::HeapInstKind::Pure(vmir::PureInst::Call(
            func_id, args,
        )));

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
        let addr = self.translate_loc_exp(&acc_exp.acc)?;
        let loc_key = self.tc.get_var_key(&addr);
        self.tc.impose(loc_key.concretizes_explicit(TcType::Addr))?;

        let amt = PureExpTranslator::new(self).translate_exp_kind(&acc_exp.perm)?;
        let amt_key = self.tc.get_var_key(&amt);
        self.tc.impose(amt_key.concretizes_explicit(TcType::Real))?;
        let perm = self.conditionalize_perm_amount(amt)?;

        self.add_heap_inst(|curr_heap| {
            vmir::HeapInstKind::Acc(AccInst {
                heap: curr_heap,
                addr,
                perm,
            })
        });

        // acc() expressions evaluate to true (bool) in the pure context
        Ok(vmir::Literal::Bool(true).into())
    }

    fn conditionalize_perm_amount(
        &mut self,
        perm: vmir::Value,
    ) -> Result<vmir::Value, TcErr<TcType>> {
        let mut perm = perm;
        let path_conds = self.path_cond_stack.clone();
        for path_cond in path_conds.into_iter().rev() {
            let PathCond::Cond(polarity, cond) = path_cond;
            let zero: vmir::Value = vmir::Literal::Real(num::BigInt::from(0).into()).into();

            let perm_key = self.tc.get_var_key(&perm);
            let zero_key = self.tc.get_var_key(&zero);
            let cond_key = self.tc.get_var_key(&cond);

            let next = match polarity {
                Polarity::Positive => self.add_inst(vmir::HeapInstKind::Pure(
                    vmir::PureInst::Ternary(cond, perm, zero),
                )),
                Polarity::Negative => self.add_inst(vmir::HeapInstKind::Pure(
                    vmir::PureInst::Ternary(cond, zero, perm),
                )),
            };
            let next_key = self.tc.get_var_key(&next);

            self.tc
                .impose(cond_key.concretizes_explicit(TcType::Bool))?;
            self.tc
                .impose(perm_key.concretizes_explicit(TcType::Real))?;
            self.tc
                .impose(zero_key.concretizes_explicit(TcType::Real))?;
            self.tc
                .impose(next_key.concretizes_explicit(TcType::Real))?;
            perm = next;
        }

        Ok(perm)
    }
}

impl<'a, 'b> PureExpBackend for HeapExpTranslCtxt<'a, 'b> {
    fn resolve_ident(&self, ident: &silver::Ident) -> vmir::Value {
        let Some(local_idx) = self.locals.get(ident) else {
            panic!("Undefined variable: {}", ident.0);
        };
        vmir::Value::Temp(*local_idx)
    }

    fn current_heap(&self) -> vmir::Value {
        self.heap.clone()
    }

    fn emit_pure_inst(&mut self, inst: vmir::PureInst) -> vmir::Value {
        self.add_inst(vmir::HeapInstKind::Pure(inst))
    }

    fn tc_mut(&mut self) -> &mut TypeChecker<TcType, vmir::Value> {
        &mut self.tc
    }

    fn translator(&self) -> &VmirTranslator {
        self.translator
    }
}
