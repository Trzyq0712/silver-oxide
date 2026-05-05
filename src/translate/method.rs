use rusttyc::{TcErr, TcKey, TypeChecker};

use crate::{
    silver,
    translate::{
        heap_exp::HeapExpTranslCtxt,
        name_resolution::DeclKind,
        pure_exp::{PureExpBackend, PureExpTranslator},
        typecheck::TcType,
        VmirTranslator,
    },
    vmir, HashMap,
};

#[derive(Debug, Clone)]
pub struct MethodTranslCtxt<'sil, 'vmir> {
    pub curr_heap: vmir::Value,
    pub entry_heap: vmir::Value,
    ensures_heap_exp: vmir::HeapExp,
    method_args: Vec<vmir::Value>,
    method_rets: Vec<vmir::Value>,
    method_ret_pos: HashMap<&'sil silver::Ident, usize>,
    pub var_map: HashMap<&'sil silver::Ident, vmir::Value>,
    var_types: HashMap<&'sil silver::Ident, vmir::Type>,

    pub tc: TypeChecker<TcType, vmir::Value>,

    pub insts: Vec<vmir::inst::InstKind>,

    pub translator: &'vmir VmirTranslator,
}

impl<'sil, 'vmir> MethodTranslCtxt<'sil, 'vmir> {
    pub fn new(
        translator: &'vmir VmirTranslator,
        signature: &'sil silver::Signature,
        contract: &'sil silver::Contract,
    ) -> Self {
        let method = translator
            .interner
            .get(signature.name.0 .0.as_str())
            .unwrap();
        let true_assert_exp = silver::HeapExp::new(Box::new(silver::ExpKind::Const(
            silver::ConstKind::Bool(true),
        )));
        let requires_heap_exp = HeapExpTranslCtxt::new_for_requires(
            translator,
            method,
            signature.args.iter().map(|a| a.idn().unwrap()),
        )
        .translate_assert_exp(
            contract
                .precondition
                .as_ref()
                .map_or(&true_assert_exp, |pre| pre),
        );
        let ensures_heap_exp = HeapExpTranslCtxt::new_for_ensures(
            translator,
            method,
            signature.args.iter().map(|a| a.idn().unwrap()),
            signature.ret.iter().filter_map(|r| r.idn()),
        )
        .translate_assert_exp(
            contract
                .postcondition
                .as_ref()
                .map_or(&true_assert_exp, |post| post),
        );

        let mut this = Self {
            curr_heap: vmir::Value::Temp(0),
            entry_heap: vmir::Value::Temp(0),
            ensures_heap_exp,
            method_args: Vec::new(),
            method_rets: Vec::new(),
            method_ret_pos: HashMap::new(),
            var_map: HashMap::new(),
            var_types: HashMap::new(),
            tc: TypeChecker::new(),
            insts: Vec::new(),
            translator,
        };

        // e0: Heap := fresh
        let empty_heap = this.add_inst(vmir::inst::InstKind::Fresh);
        this.impose_type(&empty_heap, &vmir::Type::Heap).unwrap();
        this.curr_heap = empty_heap;

        // e1..: method args
        for arg in &signature.args {
            let val = this.add_inst(vmir::inst::InstKind::Fresh);
            let ty = this.translator.translate_type(arg.ty());
            this.impose_type(&val, &ty).unwrap();
            let idn = &arg.idn().unwrap().0;
            this.var_map.insert(idn, val.clone());
            this.var_types.insert(idn, ty);
            this.method_args.push(val);
        }

        // ...: method returns
        for (idx, ret) in signature.ret.iter().enumerate() {
            let val = this.add_inst(vmir::inst::InstKind::Fresh);
            let ty = this.translator.translate_type(ret.ty());
            this.impose_type(&val, &ty).unwrap();
            let idn = &ret.idn().unwrap().0;
            this.var_map.insert(idn, val.clone());
            this.var_types.insert(idn, ty);
            this.method_ret_pos.insert(idn, idx);
            this.method_rets.push(val);
        }

        this.curr_heap = this.inline_contract(
            &requires_heap_exp,
            [&[this.curr_heap.clone()], this.method_args.as_slice()].concat(),
            ContractInlineMode::InhaleAssume,
        );
        this.entry_heap = this.curr_heap.clone();

        this
    }

    pub fn translate_statement(&mut self, stmt: &'sil silver::Statement) {
        match stmt {
            silver::Statement::Var(idns, asgn) => self.translate_var(idns, asgn.as_ref()),
            silver::Statement::Assign(lhs, assign_rhs) => self.translate_assign(lhs, assign_rhs),
            _ => unimplemented!(),
        }
    }

    fn translate_var(
        &mut self,
        idns: &'sil [silver::IdnDeclTyped],
        asgn: Option<&silver::AssignRhs>,
    ) {
        for decl in idns {
            let idn = &decl.idn.0;
            if self.var_types.contains_key(idn) {
                panic!("Duplicate variable declaration: {}", idn.0);
            }
            let ty = self.translator.translate_type(&decl.ty);
            self.var_types.insert(idn, ty);
            if asgn.is_none() {
                let val = self.add_inst(vmir::inst::InstKind::Fresh);
                let ty = self.var_types.get(idn).unwrap().clone();
                self.impose_type(&val, &ty).unwrap();
                self.var_map.insert(idn, val);
            }
        }

        let Some(asgn) = asgn else { return };

        let lhs = idns
            .iter()
            .map(|idn| silver::AssignLhs::Ident(idn.idn.0.clone()))
            .collect::<Vec<_>>();
        self.translate_assign(&lhs, asgn);
    }

    fn translate_assign(&mut self, lhs: &[silver::AssignLhs], assign_rhs: &silver::AssignRhs) {
        match assign_rhs {
            silver::AssignRhs::Exp(exp) => {
                let rhs = self.translate_pure_exp(exp);
                let [lhs] = lhs else {
                    unimplemented!("Tuple assignment is not implemented");
                };
                let lhs_ident = self.translate_assign_ident(lhs);
                let declared = self.declared_type(lhs_ident).clone();
                self.impose_type(&rhs, &declared).unwrap();
                self.bind_ident(lhs_ident, rhs);
            }
            silver::AssignRhs::Call(idn, args) => self.translate_call(lhs, idn, args),
            silver::AssignRhs::New(_) => unimplemented!(),
        }
    }

    fn translate_call(
        &mut self,
        lhs: &[silver::AssignLhs],
        call_tgt: &silver::Ident,
        args: &[silver::Exp],
    ) {
        let memid = self.translator.interner.get(call_tgt.0.as_str()).unwrap();
        let call_tgt_type = self.translator.name_kinds[memid];
        match call_tgt_type {
            DeclKind::Method => self.translate_method_call(lhs, memid, args),
            _ => unimplemented!(),
        }
    }

    fn translate_lhs_exp(&mut self, exp: &silver::ExpKind) -> vmir::Value {
        match exp {
            silver::ExpKind::Ident(idn) => self.var_map.get(&idn).unwrap().clone(),
            silver::ExpKind::Field(exp, idn) => unimplemented!(),
            _ => panic!("Assign LHS can be an identifier or a field access only"),
        }
    }

    fn translate_assign_ident<'a>(&self, lhs: &'a silver::AssignLhs) -> &'a silver::Ident {
        match lhs {
            silver::AssignLhs::Ident(idn) => idn,
            silver::AssignLhs::Field(_, _) => unimplemented!(),
        }
    }

    fn freshen_ident_binding(&mut self, ident: &silver::Ident) -> vmir::Value {
        let Some((canonical, ty)) = self.var_types.get_key_value(ident) else {
            panic!("Undefined variable: {}", ident.0);
        };
        let canonical = *canonical;
        let ty = ty.clone();
        let fresh = self.add_inst(vmir::inst::InstKind::Fresh);
        self.impose_type(&fresh, &ty).unwrap();
        self.bind_ident(canonical, fresh.clone());
        fresh
    }

    fn declared_type(&self, ident: &silver::Ident) -> &vmir::Type {
        self.var_types
            .get(ident)
            .unwrap_or_else(|| panic!("Undefined variable: {}", ident.0))
    }

    fn bind_ident(&mut self, ident: &silver::Ident, value: vmir::Value) {
        let Some((canonical, _)) = self.var_types.get_key_value(ident) else {
            panic!("Undefined variable: {}", ident.0);
        };
        let canonical = *canonical;
        self.var_map.insert(canonical, value.clone());
        if let Some(idx) = self.method_ret_pos.get(canonical) {
            self.method_rets[*idx] = value;
        }
    }

    fn translate_exp(&mut self, exp: &silver::ExpKind) -> vmir::Value {
        PureExpTranslator::new(self)
            .translate_exp_kind(exp)
            .unwrap_or_else(|e| panic!("Method expression type checking failed: {:?}", e))
    }

    fn translate_pure_exp(&mut self, exp: &silver::PureExp) -> vmir::Value {
        PureExpTranslator::new(self)
            .translate_pure_exp(exp)
            .unwrap_or_else(|e| panic!("Method expression type checking failed: {:?}", e))
    }

    fn translate_method_call(
        &mut self,
        lhs: &[silver::AssignLhs],
        memid: vmir::MemberId,
        args: &[silver::Exp],
    ) {
        let args = args
            .iter()
            .map(|arg| self.translate_exp(arg))
            .collect::<Vec<_>>();

        let callee_sig = self.translator.signatures.method_sig(memid);
        assert_eq!(
            callee_sig.args.len(),
            args.len(),
            "Method call arity mismatch for args"
        );
        assert_eq!(
            callee_sig.ret.len(),
            lhs.len(),
            "Method call arity mismatch for returns"
        );

        for (arg, ty) in args.iter().zip(callee_sig.args.iter()) {
            self.impose_type(arg, ty).unwrap();
        }
        let rets = lhs
            .iter()
            .zip(callee_sig.ret.iter())
            .map(|(lhs_exp, ret_ty)| {
                let lhs_ident = self.translate_assign_ident(lhs_exp);
                let ret_val = self.freshen_ident_binding(lhs_ident);
                self.impose_type(&ret_val, ret_ty).unwrap();
                ret_val
            })
            .collect::<Vec<_>>();
        for (ret, ty) in rets.iter().zip(callee_sig.ret.iter()) {
            self.impose_type(ret, ty).unwrap();
        }

        let req_memid = self.translator.method_requires_callable_id(memid);
        let ens_memid = self.translator.method_ensures_callable_id(memid);

        let exhale = vmir::inst::InstKind::Call(
            req_memid,
            [&[self.curr_heap.clone()], args.as_slice()].concat(),
        );
        let exhale_heap = self.add_inst(exhale);
        self.impose_type(&exhale_heap, &vmir::Type::Heap).unwrap();

        let inhale = vmir::inst::InstKind::Call(
            ens_memid,
            [
                &[exhale_heap.clone(), exhale_heap],
                args.as_slice(),
                rets.as_slice(),
            ]
            .concat(),
        );
        self.curr_heap = self.add_inst(inhale);
        let curr_heap = self.curr_heap.clone();
        self.impose_type(&curr_heap, &vmir::Type::Heap).unwrap();
    }

    fn add_inst(&mut self, inst: vmir::inst::InstKind) -> vmir::Value {
        self.insts.push(inst);
        vmir::Value::Temp(self.insts.len() - 1)
    }

    fn resolve_contract_value(&self, values: &[vmir::Value], value: &vmir::Value) -> vmir::Value {
        match value {
            vmir::Value::Temp(idx) => values
                .get(*idx)
                .unwrap_or_else(|| panic!("Invalid contract temporary index {idx}"))
                .clone(),
            vmir::Value::Literal(lit) => vmir::Value::Literal(lit.clone()),
        }
    }

    fn resolve_contract_pure_inst(
        &self,
        values: &[vmir::Value],
        pure: &vmir::PureInst,
    ) -> vmir::PureInst {
        match pure {
            vmir::PureInst::Unary(op, value) => {
                vmir::PureInst::Unary(*op, self.resolve_contract_value(values, value))
            }
            vmir::PureInst::Binary(op, lhs, rhs) => vmir::PureInst::Binary(
                *op,
                self.resolve_contract_value(values, lhs),
                self.resolve_contract_value(values, rhs),
            ),
            vmir::PureInst::Ternary(cond, then_val, else_val) => vmir::PureInst::Ternary(
                self.resolve_contract_value(values, cond),
                self.resolve_contract_value(values, then_val),
                self.resolve_contract_value(values, else_val),
            ),
            vmir::PureInst::Call(member, args) => vmir::PureInst::Call(
                *member,
                args.iter()
                    .map(|arg| self.resolve_contract_value(values, arg))
                    .collect(),
            ),
            vmir::PureInst::Heap(heap_dep) => vmir::PureInst::Heap(vmir::HeapDepInst {
                heap: self.resolve_contract_value(values, &heap_dep.heap),
                kind: match &heap_dep.kind {
                    vmir::HeapDepInstKind::Perm(addr) => {
                        vmir::HeapDepInstKind::Perm(self.resolve_contract_value(values, addr))
                    }
                    vmir::HeapDepInstKind::Deref(addr) => {
                        vmir::HeapDepInstKind::Deref(self.resolve_contract_value(values, addr))
                    }
                },
            }),
        }
    }

    fn negate_real(&mut self, value: vmir::Value) -> vmir::Value {
        let zero = vmir::Literal::Real(num::BigInt::from(0).into()).into();
        let delta = self.add_inst(vmir::inst::InstKind::Binary(
            vmir::BinOp::Minus,
            zero,
            value,
        ));
        self.impose_type(&delta, &vmir::Type::Real).unwrap();
        delta
    }

    fn inline_contract(
        &mut self,
        heap_exp: &vmir::HeapExp,
        inputs: Vec<vmir::Value>,
        mode: ContractInlineMode,
    ) -> vmir::Value {
        assert_eq!(
            heap_exp.input_types.len(),
            inputs.len(),
            "Contract input count mismatch"
        );

        let mut values = inputs;
        for heap_inst in &heap_exp.insts {
            let result = match &heap_inst.kind {
                vmir::HeapInstKind::Pure(pure_inst) => {
                    let pure_inst = self.resolve_contract_pure_inst(&values, pure_inst);
                    self.add_inst(lower_pure_inst(pure_inst))
                }
                vmir::HeapInstKind::Acc(acc) => {
                    let heap = self.resolve_contract_value(&values, &acc.heap);
                    let addr = self.resolve_contract_value(&values, &acc.addr);
                    let perm = self.resolve_contract_value(&values, &acc.perm);
                    let perm = match mode {
                        ContractInlineMode::InhaleAssume => perm,
                        ContractInlineMode::ExhaleAssert => self.negate_real(perm),
                    };
                    self.add_inst(vmir::inst::InstKind::Heap(
                        heap,
                        addr,
                        vmir::inst::HeapInst::PermMod(perm),
                    ))
                }
            };
            self.impose_type(&result, &heap_inst.ty).unwrap();
            values.push(result);
        }

        let cond = self.resolve_contract_value(&values, &heap_exp.res_pure);
        self.impose_type(&cond, &vmir::Type::Bool).unwrap();
        let check = self.add_inst(match mode {
            ContractInlineMode::InhaleAssume => vmir::inst::InstKind::Assume(cond),
            ContractInlineMode::ExhaleAssert => vmir::inst::InstKind::Assert(cond),
        });
        self.impose_type(&check, &vmir::Type::Bool).unwrap();

        let heap = self.resolve_contract_value(&values, &heap_exp.res_impure);
        self.impose_type(&heap, &vmir::Type::Heap).unwrap();
        heap
    }

    fn impose_type(&mut self, val: &vmir::Value, ty: &vmir::Type) -> Result<(), TcErr<TcType>> {
        let key = self.tc.get_var_key(val);
        self.impose_type_key(ty, key)
    }

    fn impose_type_key(&mut self, ty: &vmir::Type, key: TcKey) -> Result<(), TcErr<TcType>> {
        self.tc.impose(key.concretizes_explicit(ty.into()))?;
        match ty {
            vmir::Type::Addr(inner) => {
                let child = self.tc.get_child_key(key, 0)?;
                self.impose_type_key(inner, child)
            }
            _ => Ok(()),
        }
    }

    pub fn finalize(mut self) -> vmir::inst::Method {
        let ensures_heap_exp = self.ensures_heap_exp.clone();
        self.curr_heap = self.inline_contract(
            &ensures_heap_exp,
            [
                &[self.curr_heap.clone(), self.entry_heap.clone()],
                self.method_args.as_slice(),
                self.method_rets.as_slice(),
            ]
            .concat(),
            ContractInlineMode::ExhaleAssert,
        );

        let inst_key: Vec<_> = self
            .insts
            .into_iter()
            .enumerate()
            .map(|(idx, inst)| {
                let temp = vmir::Value::Temp(idx);
                let key = self.tc.get_var_key(&temp);
                (inst, key)
            })
            .collect();

        let type_table = self.tc.type_check().unwrap_or_else(|e| {
            panic!("Method type checking failed: {:?}", e);
        });

        vmir::inst::Method(
            inst_key
                .into_iter()
                .map(|(kind, key)| vmir::inst::Inst {
                    kind,
                    ty: type_table[&key].clone(),
                })
                .collect(),
        )
    }
}

#[derive(Debug, Clone, Copy)]
enum ContractInlineMode {
    InhaleAssume,
    ExhaleAssert,
}

impl<'sil, 'vmir> PureExpBackend for MethodTranslCtxt<'sil, 'vmir> {
    fn resolve_ident(&self, ident: &silver::Ident) -> vmir::Value {
        self.var_map
            .get(ident)
            .unwrap_or_else(|| panic!("Undefined variable: {}", ident.0))
            .clone()
    }

    fn current_heap(&self) -> vmir::Value {
        self.curr_heap.clone()
    }

    fn old_heap(&self, label: Option<&silver::Ident>) -> Option<vmir::Value> {
        label.is_none().then(|| self.entry_heap.clone())
    }

    fn emit_pure_inst(&mut self, inst: vmir::PureInst) -> vmir::Value {
        self.add_inst(lower_pure_inst(inst))
    }

    fn tc_mut(&mut self) -> &mut TypeChecker<TcType, vmir::Value> {
        &mut self.tc
    }

    fn translator(&self) -> &VmirTranslator {
        self.translator
    }
}

fn lower_pure_inst(inst: vmir::PureInst) -> vmir::inst::InstKind {
    match inst {
        vmir::PureInst::Unary(op, value) => vmir::inst::InstKind::Unary(op, value),
        vmir::PureInst::Binary(op, lhs, rhs) => vmir::inst::InstKind::Binary(op, lhs, rhs),
        vmir::PureInst::Ternary(cond, then_val, else_val) => {
            vmir::inst::InstKind::Ternary(cond, then_val, else_val)
        }
        vmir::PureInst::Call(member, args) => vmir::inst::InstKind::Call(member, args),
        vmir::PureInst::Heap(heap_dep) => match heap_dep.kind {
            vmir::HeapDepInstKind::Perm(addr) => {
                vmir::inst::InstKind::Heap(heap_dep.heap, addr, vmir::inst::HeapInst::Perm)
            }
            vmir::HeapDepInstKind::Deref(addr) => {
                vmir::inst::InstKind::Heap(heap_dep.heap, addr, vmir::inst::HeapInst::Deref)
            }
        },
    }
}
