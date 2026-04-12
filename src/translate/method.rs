use rusttyc::{TcErr, TcKey, TypeChecker};

use crate::{
    silver,
    translate::{name_resolution::DeclKind, typecheck::TcType, VmirTranslator},
    vmir, HashMap,
};

#[derive(Debug, Clone)]
pub struct MethodTranslCtxt<'sil, 'vmir> {
    pub curr_heap: vmir::Value,
    pub post_inhale_heap: vmir::Value,
    exhale_member: vmir::MemberId,
    method_args: Vec<vmir::Value>,
    method_rets: Vec<vmir::Value>,
    method_ret_pos: HashMap<&'sil silver::Ident, usize>,
    pub var_map: HashMap<&'sil silver::Ident, vmir::Value>,
    var_types: HashMap<&'sil silver::Ident, vmir::Type>,

    pub tc: TypeChecker<TcType, vmir::Value>,

    pub insts: Vec<vmir::method::InstKind>,

    pub translator: &'vmir VmirTranslator,
}

impl<'sil, 'vmir> MethodTranslCtxt<'sil, 'vmir> {
    pub fn new(translator: &'vmir VmirTranslator, signature: &'sil silver::Signature) -> Self {
        let req_member = translator
            .interner
            .get(format!("{}@requires", signature.name.0 .0.as_str()))
            .unwrap();
        let exhale_member = translator
            .interner
            .get(format!("{}@ensures", signature.name.0 .0.as_str()))
            .unwrap();

        let mut this = Self {
            curr_heap: vmir::Value::Temp(0),
            post_inhale_heap: vmir::Value::Temp(0),
            exhale_member,
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
        let empty_heap = this.add_inst(vmir::method::InstKind::Fresh);
        this.impose_type(&empty_heap, &vmir::Type::Heap).unwrap();
        this.curr_heap = empty_heap;

        // e1..: method args
        for arg in &signature.args {
            let val = this.add_inst(vmir::method::InstKind::Fresh);
            let ty = this.translator.translate_type(arg.ty());
            this.impose_type(&val, &ty).unwrap();
            let idn = &arg.idn().unwrap().0;
            this.var_map.insert(idn, val.clone());
            this.var_types.insert(idn, ty);
            this.method_args.push(val);
        }

        // ...: method returns
        for (idx, ret) in signature.ret.iter().enumerate() {
            let val = this.add_inst(vmir::method::InstKind::Fresh);
            let ty = this.translator.translate_type(ret.ty());
            this.impose_type(&val, &ty).unwrap();
            let idn = &ret.idn().unwrap().0;
            this.var_map.insert(idn, val.clone());
            this.var_types.insert(idn, ty);
            this.method_ret_pos.insert(idn, idx);
            this.method_rets.push(val);
        }

        // inhale method precondition: inhale m@requires(heap, ...args)
        let inhale = vmir::method::InstKind::HeapOp(
            vmir::method::HeapOp::Inhale,
            req_member,
            [&[this.curr_heap.clone()], this.method_args.as_slice()].concat(),
        );
        let post_inhale_heap = this.add_inst(inhale);
        this.impose_type(&post_inhale_heap, &vmir::Type::Heap)
            .unwrap();
        this.post_inhale_heap = post_inhale_heap.clone();
        this.curr_heap = post_inhale_heap;

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
                let val = self.add_inst(vmir::method::InstKind::Fresh);
                let ty = self.var_types.get(idn).unwrap().clone();
                self.impose_type(&val, &ty).unwrap();
                self.var_map.insert(idn, val);
            }
        }

        let Some(asgn) = asgn else { return };

        let lhs = idns
            .iter()
            .map(|idn| Box::new(silver::ExpKind::Ident(idn.idn.0.clone())))
            .collect::<Vec<_>>();
        self.translate_assign(&lhs, asgn);
    }

    fn translate_assign(&mut self, lhs: &[silver::Exp], assign_rhs: &silver::AssignRhs) {
        match assign_rhs {
            silver::AssignRhs::Exp(exp) => {
                let rhs = self.translate_exp(exp);
                let [lhs] = lhs else {
                    unimplemented!("Tuple assignment is not implemented");
                };
                let lhs_ident = self.translate_assign_ident(lhs.as_ref());
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
        lhs: &[silver::Exp],
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

    fn translate_assign_ident<'a>(&self, exp: &'a silver::ExpKind) -> &'a silver::Ident {
        match exp {
            silver::ExpKind::Ident(idn) => idn,
            silver::ExpKind::Field(exp, idn) => unimplemented!(),
            _ => panic!("Assign LHS can be an identifier or a field access only"),
        }
    }

    fn freshen_ident_binding(&mut self, ident: &silver::Ident) -> vmir::Value {
        let Some((canonical, ty)) = self.var_types.get_key_value(ident) else {
            panic!("Undefined variable: {}", ident.0);
        };
        let canonical = *canonical;
        let ty = ty.clone();
        let fresh = self.add_inst(vmir::method::InstKind::Fresh);
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
        match exp {
            silver::ExpKind::Ident(idn) => self.var_map.get(&idn).unwrap().clone(),
            silver::ExpKind::Const(_) => unimplemented!(),
            silver::ExpKind::BinOp(silver::BinOp::Plus, lhs, rhs) => {
                let lhs = self.translate_exp(lhs);
                let rhs = self.translate_exp(rhs);
                let lhs_key = self.tc.get_var_key(&lhs);
                let rhs_key = self.tc.get_var_key(&rhs);
                let val = self.add_inst(vmir::method::InstKind::BinOp(vmir::BinOp::Plus, lhs, rhs));
                let v_key = self.tc.get_var_key(&val);
                self.tc
                    .impose(lhs_key.concretizes_explicit(TcType::Numeric))
                    .unwrap();
                self.tc
                    .impose(rhs_key.concretizes_explicit(TcType::Numeric))
                    .unwrap();
                self.tc
                    .impose(v_key.concretizes_explicit(TcType::Numeric))
                    .unwrap();
                val
            }
            _ => unimplemented!(),
        }
    }

    fn translate_method_call(
        &mut self,
        lhs: &[silver::Exp],
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
                let lhs_ident = self.translate_assign_ident(lhs_exp.as_ref());
                let ret_val = self.freshen_ident_binding(lhs_ident);
                self.impose_type(&ret_val, ret_ty).unwrap();
                ret_val
            })
            .collect::<Vec<_>>();
        for (ret, ty) in rets.iter().zip(callee_sig.ret.iter()) {
            self.impose_type(ret, ty).unwrap();
        }

        let req_memid = self
            .translator
            .interner
            .get(format!("{}@requires", self.translator.interner.resolve(&memid)).as_str())
            .unwrap();

        let ens_memid = self
            .translator
            .interner
            .get(format!("{}@ensures", self.translator.interner.resolve(&memid)).as_str())
            .unwrap();

        let exhale = vmir::method::InstKind::HeapOp(
            vmir::method::HeapOp::Exhale,
            req_memid,
            [&[self.curr_heap.clone()], args.as_slice()].concat(),
        );
        let exhale_heap = self.add_inst(exhale);
        self.impose_type(&exhale_heap, &vmir::Type::Heap).unwrap();
        let old_heap = self.curr_heap.clone();

        let inhale = vmir::method::InstKind::HeapOp(
            vmir::method::HeapOp::Inhale,
            ens_memid,
            [&[exhale_heap, old_heap], args.as_slice(), rets.as_slice()].concat(),
        );
        self.curr_heap = self.add_inst(inhale);
        let curr_heap = self.curr_heap.clone();
        self.impose_type(&curr_heap, &vmir::Type::Heap).unwrap();
    }

    fn add_inst(&mut self, inst: vmir::method::InstKind) -> vmir::Value {
        self.insts.push(inst);
        vmir::Value::Temp(self.insts.len() - 1)
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

    pub fn finalize(mut self) -> vmir::method::Method {
        // Exhale method postcondition: exhale m@ensures(curr_heap, old_heap, ...args, ...rets)
        let final_exhale = vmir::method::InstKind::HeapOp(
            vmir::method::HeapOp::Exhale,
            self.exhale_member,
            [
                &[self.curr_heap.clone(), self.post_inhale_heap.clone()],
                self.method_args.as_slice(),
                self.method_rets.as_slice(),
            ]
            .concat(),
        );
        let final_heap = self.add_inst(final_exhale);
        self.impose_type(&final_heap, &vmir::Type::Heap).unwrap();

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

        vmir::method::Method(
            inst_key
                .into_iter()
                .map(|(kind, key)| vmir::method::Inst {
                    kind,
                    ty: type_table[&key].clone(),
                })
                .collect(),
        )
    }
}
