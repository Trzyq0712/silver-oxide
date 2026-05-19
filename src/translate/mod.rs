use crate::translate::global_resolver::{
    DuplicateGlobalError, GlobalResolver, GlobalResolverBuilder,
};
use crate::translate::resource::MethodContractResources;
use crate::translate::signature_resolver::{SignatureResolver, SignatureResolverBuilder};
use crate::vmir::{
    self, Declaration, HeapInst, HeapVal, Inst, MemberId, PureInst, Resource, Type, Val,
};
use crate::{HashMap, silver};
use lasso::Key;
use typed_index_collections::{TiVec, ti_vec};

pub mod global_resolver;
pub mod signature_resolver;

pub mod heap_exp;
pub mod inst;
pub mod pure_exp;
pub mod resource;
pub mod signatures;
pub mod typecheck;
pub use typecheck::VmirTc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IdentifierError {
    DuplicateName { name: String },
    CallResolution { message: String },
}

impl std::fmt::Display for IdentifierError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IdentifierError::DuplicateName { name } => {
                write!(f, "Duplicate declaration: '{name}'")
            }
            IdentifierError::CallResolution { message } => write!(f, "{message}"),
        }
    }
}

impl std::error::Error for IdentifierError {}

#[derive(Debug, Clone)]
pub struct VmirSymbols {
    pub vmir_interner: lasso::Rodeo<vmir::MemberId>,
    pub resolver: GlobalResolver,
    pub signatures: SignatureResolver,
}

#[derive(Debug)]
pub struct VmirTranslator {
    decls: TiVec<vmir::MemberId, Option<vmir::Declaration>>,
    vmir_interner: lasso::Rodeo<vmir::MemberId>,
    pub(crate) resolver: GlobalResolver,
    pub(crate) signatures: SignatureResolver,
}

impl VmirTranslator {
    pub fn new(symbols: VmirSymbols) -> Self {
        let count = symbols.vmir_interner.len();
        Self {
            decls: ti_vec![None; count],
            vmir_interner: symbols.vmir_interner,
            resolver: symbols.resolver,
            signatures: symbols.signatures,
        }
    }

    pub fn translate(program: &silver::Program) -> Result<vmir::Program, Vec<IdentifierError>> {
        let mut program = program.clone();
        silver::resolve_call_kinds(&mut program).map_err(map_call_resolution_errors)?;

        let mut global_builder = GlobalResolverBuilder::new();
        for decl in &program.0 {
            match decl {
                silver::Declaration::Field(field) => {
                    global_builder
                        .add_field(field)
                        .map_err(map_duplicate_error)?;
                }
                silver::Declaration::Function(function) => {
                    global_builder
                        .add_function(function)
                        .map_err(map_duplicate_error)?;
                }
                silver::Declaration::Predicate(predicate) => {
                    global_builder
                        .add_predicate(predicate)
                        .map_err(map_duplicate_error)?;
                }
                silver::Declaration::Method(method) => {
                    global_builder
                        .add_method(method)
                        .map_err(map_duplicate_error)?;
                }
                silver::Declaration::Domain(domain) => {
                    global_builder
                        .add_domain(domain)
                        .map_err(map_duplicate_error)?;
                }
                silver::Declaration::DomainElement(domain_elem) => {
                    if let silver::DomainElementKind::Function(f) = &domain_elem.kind {
                        global_builder
                            .add_domain_function(f)
                            .map_err(map_duplicate_error)?;
                    }
                }
                silver::Declaration::Adt(adt) => {
                    global_builder.add_adt(adt).map_err(map_duplicate_error)?;
                }
                silver::Declaration::AdtConstructor(ctor) => {
                    global_builder
                        .add_adt_constructor(ctor)
                        .map_err(map_duplicate_error)?;
                }
                _ => {}
            };
        }
        let (resolver, vmir_interner) = global_builder.finalize();

        let mut sig_builder = SignatureResolverBuilder::new();
        for decl in &program.0 {
            match decl {
                silver::Declaration::Field(field) => {
                    let id = resolver.resolve_field(&field.0.idn.0).unwrap().id;
                    let ret = translate_type_with_resolver(&resolver, &field.0.ty);
                    sig_builder.add_function(id, vec![Type::Ref], Type::Addr(Box::new(ret)));
                }
                silver::Declaration::Function(function) => {
                    let id = resolver
                        .resolve_function(&function.signature.name.0)
                        .unwrap()
                        .id;
                    let args = function
                        .signature
                        .args
                        .iter()
                        .map(|arg| translate_type_with_resolver(&resolver, arg.ty()))
                        .collect::<Vec<_>>();
                    let ret = function
                        .signature
                        .ret
                        .first()
                        .map(|r| translate_type_with_resolver(&resolver, r.ty()))
                        .unwrap_or(Type::Bool);
                    sig_builder.add_function(id, args, ret);
                }
                silver::Declaration::Predicate(pred) => {
                    let resolved = resolver.resolve_predicate(&pred.signature.name.0).unwrap();
                    let args = pred
                        .signature
                        .args
                        .iter()
                        .map(|arg| translate_type_with_resolver(&resolver, arg.ty()))
                        .collect::<Vec<_>>();
                    sig_builder.add_function(
                        resolved.id,
                        args,
                        Type::Addr(Box::new(Type::Domain(resolved.snap))),
                    );
                }
                silver::Declaration::Method(method) => {
                    let resolved = resolver.resolve_method(&method.signature.name.0).unwrap();
                    let args = method
                        .signature
                        .args
                        .iter()
                        .map(|arg| translate_type_with_resolver(&resolver, arg.ty()))
                        .collect::<Vec<_>>();
                    let ret = method
                        .signature
                        .ret
                        .iter()
                        .map(|r| translate_type_with_resolver(&resolver, r.ty()))
                        .collect::<Vec<_>>();
                    if let Some(req_id) = resolved.precond {
                        sig_builder.add_resource(req_id, args.clone());
                    }
                    if let Some(ens_id) = resolved.postcond {
                        let mut full = args;
                        full.extend(ret);
                        sig_builder.add_resource(ens_id, full);
                    }
                }
                _ => {}
            }
        }

        let symbols = VmirSymbols {
            vmir_interner,
            resolver,
            signatures: sig_builder.finalize(),
        };
        let mut translator = Self::new(symbols);
        translator.translate_program(&program);

        let decls = translator
            .decls
            .into_iter()
            .map(|decl| decl.unwrap_or(Declaration::DomainElement))
            .collect();
        Ok(vmir::Program {
            decls,
            interner: translator.vmir_interner,
        })
    }

    fn translate_program(&mut self, program: &silver::Program) {
        for decl in &program.0 {
            match decl {
                silver::Declaration::Field(field) => self.translate_field(field),
                silver::Declaration::Predicate(predicate) => self.translate_predicate(predicate),
                silver::Declaration::Method(method) => self.translate_method(method),
                silver::Declaration::Function(function) => self.translate_function(function),
                silver::Declaration::Domain(domain) => {
                    let id = self.resolver.resolve_member_id(&domain.name.0).unwrap();
                    self.add_decl(id, Declaration::Domain(vmir::Domain {}));
                }
                silver::Declaration::DomainElement(domain_element) => {
                    if let silver::DomainElementKind::Function(f) = &domain_element.kind {
                        let id = self
                            .resolver
                            .resolve_member_id(&f.signature.name.0)
                            .unwrap();
                        self.add_decl(id, Declaration::DomainElement);
                    }
                }
                silver::Declaration::Adt(adt) => {
                    let id = self.resolver.resolve_member_id(&adt.name.0).unwrap();
                    self.add_decl(id, Declaration::Adt(vmir::Adt {}));
                }
                silver::Declaration::AdtConstructor(ctor) => {
                    let id = self
                        .resolver
                        .resolve_member_id(&ctor.signature.name.0)
                        .unwrap();
                    self.add_decl(id, Declaration::AdtConstructor);
                }
                _ => {}
            }
        }
    }

    fn add_decl(&mut self, id: MemberId, decl: Declaration) {
        if id.into_usize() >= self.decls.len() {
            while id.into_usize() >= self.decls.len() {
                self.decls.push(None);
            }
        }
        self.decls[id] = Some(decl);
    }

    pub(crate) fn translate_type(&self, ty: &silver::Type) -> Type {
        translate_type_with_resolver(&self.resolver, ty)
    }

    fn translate_field(&mut self, field: &silver::Field) {
        let id = self.resolver.resolve_field(&field.0.idn.0).unwrap().id;
        let ret = self
            .signatures
            .resolve_function(id)
            .unwrap_or_else(|_| panic!("missing field signature: {:?}", field.0.idn.0))
            .ret
            .clone();
        self.add_decl(
            id,
            Declaration::Function(vmir::Function {
                params: vec![Type::Ref],
                ret,
            }),
        );
    }

    fn translate_predicate(&mut self, pred: &silver::Predicate) {
        let resolved = self
            .resolver
            .resolve_predicate(&pred.signature.name.0)
            .unwrap();
        let pred_id = resolved.id;
        let snap_id = resolved.snap;
        self.add_decl(snap_id, Declaration::Domain(vmir::Domain {}));
        let sig = self.signatures.resolve_function(pred_id).unwrap();
        self.add_decl(
            pred_id,
            Declaration::Function(vmir::Function {
                params: sig.args.clone(),
                ret: sig.ret.clone(),
            }),
        );
    }

    fn translate_function(&mut self, function: &silver::Function) {
        let id = self
            .resolver
            .resolve_function(&function.signature.name.0)
            .unwrap()
            .id;
        let sig = self.signatures.resolve_function(id).unwrap();
        self.add_decl(
            id,
            Declaration::Function(vmir::Function {
                params: sig.args.clone(),
                ret: sig.ret.clone(),
            }),
        );
    }

    fn translate_method(&mut self, method: &silver::Method) {
        let method_id = self
            .resolver
            .resolve_method(&method.signature.name.0)
            .unwrap()
            .id;
        let MethodContractResources { requires, ensures } =
            resource::translate_method_contracts(self, method_id, method);
        let mut requires_id = None;
        if let Some((id, requires_res)) = requires {
            self.add_decl(id, Declaration::Resource(requires_res));
            requires_id = Some(id);
        }
        let mut ensures_id = None;
        if let Some((id, ensures_res)) = ensures {
            self.add_decl(id, Declaration::Resource(ensures_res));
            ensures_id = Some(id);
        }

        if method.body.is_none() {
            return;
        }

        let mut builder = MethodBuilder::new(self);
        for arg in &method.signature.args {
            if let Some(idn) = arg.idn() {
                let ty = self.translate_type(arg.ty());
                let v = builder.emit_fresh(ty);
                builder.bind(idn, v.clone());
                builder.args.push(v);
            }
        }
        for ret in &method.signature.ret {
            if let Some(idn) = ret.idn() {
                let ty = self.translate_type(ret.ty());
                let v = builder.emit_fresh(ty);
                builder.bind(idn, v.clone());
                builder.rets.push(v);
            }
        }

        if let Some(requires_id) = requires_id {
            builder.apply_resource(requires_id, builder.args.clone(), ContractMode::AddAssume);
        }
        builder.entry_heap = builder.current_heap.clone();

        let body = method.body.as_ref().unwrap();
        for stmt in &body.0 {
            builder.translate_statement(stmt);
        }

        if let Some(ensures_id) = ensures_id {
            let mut ensure_args = builder.args.clone();
            ensure_args.extend(builder.rets.clone());
            builder.apply_resource(ensures_id, ensure_args, ContractMode::SubAssert);
        }

        self.add_decl(
            method_id,
            Declaration::Method(vmir::Method {
                insts: builder.insts,
            }),
        );
    }
}

#[derive(Debug, Clone, Copy)]
enum ContractMode {
    AddAssume,
    SubAssert,
}

struct MethodBuilder<'a> {
    translator: &'a VmirTranslator,
    insts: Vec<Inst>,
    env: HashMap<String, Val>,
    next_temp: usize,
    current_heap: HeapVal,
    entry_heap: HeapVal,
    args: Vec<Val>,
    rets: Vec<Val>,
}

impl<'a> MethodBuilder<'a> {
    fn new(translator: &'a VmirTranslator) -> Self {
        Self {
            translator,
            insts: Vec::new(),
            env: HashMap::new(),
            next_temp: 0,
            current_heap: HeapVal::Empty,
            entry_heap: HeapVal::Empty,
            args: Vec::new(),
            rets: Vec::new(),
        }
    }

    fn bind(&mut self, idn: &silver::IdnDecl, v: Val) {
        self.env.insert(idn.0.0.clone(), v);
    }

    fn emit_fresh(&mut self, ty: Type) -> Val {
        let idx = self.next_temp;
        self.next_temp += 1;
        self.insts.push(Inst::Pure(ty, PureInst::Fresh));
        Val::Temp(idx)
    }

    fn emit_pure(&mut self, ty: Type, pure: PureInst) -> Val {
        let idx = self.next_temp;
        self.next_temp += 1;
        self.insts.push(Inst::Pure(ty, pure));
        Val::Temp(idx)
    }

    fn emit_heap(&mut self, heap: HeapInst) -> HeapVal {
        let idx = self.next_temp;
        self.next_temp += 1;
        self.insts.push(Inst::Heap(heap));
        HeapVal::Temp(idx)
    }

    fn translate_statement(&mut self, stmt: &silver::Statement) {
        match stmt {
            silver::Statement::Var(decls, init) => {
                for decl in decls {
                    let v = self.emit_fresh(self.translator.translate_type(&decl.ty));
                    self.bind(&decl.idn, v);
                }
                if let Some(rhs) = init {
                    let lhs = decls
                        .iter()
                        .map(|d| silver::AssignLhs::Ident(d.idn.0.clone()))
                        .collect::<Vec<_>>();
                    self.translate_assign(&lhs, rhs);
                }
            }
            silver::Statement::Assign(lhs, rhs) => self.translate_assign(lhs, rhs),
            _ => {}
        }
    }

    fn translate_assign(&mut self, lhs: &[silver::AssignLhs], rhs: &silver::AssignRhs) {
        match rhs {
            silver::AssignRhs::Exp(exp) => {
                let v = self.translate_exp(exp);
                if let [silver::AssignLhs::Ident(idn)] = lhs {
                    self.env.insert(idn.0.clone(), v);
                }
            }
            silver::AssignRhs::Call(..) => todo!(),
            // silver::AssignRhs::Call(callee, args) => {
            //     let callee_id = self
            //         .translator
            //         .resolver
            //         .resolve_member_id(callee)
            //         .unwrap_or_else(|_| panic!("unknown call target: {}", callee.0));
            //     let arg_vals = args
            //         .iter()
            //         .map(|a| self.translate_exp(a))
            //         .collect::<Vec<_>>();
            //     let method_resolved = self
            //         .translator
            //         .resolver
            //         .resolve_method_id(callee_id)
            //         .unwrap();
            //     let mut lhs_vals = Vec::new();
            //     for (lhs_item, ret_ty) in lhs.iter().zip(method_sig.ret.iter()) {
            //         if let silver::AssignLhs::Ident(idn) = lhs_item {
            //             let v = self.emit_fresh(ret_ty.clone());
            //             self.env.insert(idn.0.clone(), v.clone());
            //             lhs_vals.push(v);
            //         }
            //     }
            //
            //     if let Some(req_id) = method_resolved.precond {
            //         self.apply_resource(req_id, arg_vals.clone(), ContractMode::SubAssert);
            //     }
            //
            //     if let Some(ens_id) = method_resolved.postcond {
            //         let mut ens_args = arg_vals;
            //         ens_args.extend(lhs_vals);
            //         self.apply_resource(ens_id, ens_args, ContractMode::AddAssume);
            //     }
            // }
            silver::AssignRhs::New(_) => {}
        }
    }

    fn translate_exp(&mut self, exp: &silver::Exp) -> Val {
        match exp.as_ref() {
            silver::ExpKind::Const(c) => match c {
                silver::ConstKind::Bool(b) => Val::Literal(vmir::Literal::Bool(*b)),
                silver::ConstKind::Int(i) => Val::Literal(vmir::Literal::Int(i.clone())),
                silver::ConstKind::Real(r) => Val::Literal(vmir::Literal::Real(r.clone())),
                silver::ConstKind::Null => Val::Literal(vmir::Literal::Null),
                _ => unimplemented!(),
            },
            silver::ExpKind::Ident(idn) => self.env.get(&idn.0).cloned().unwrap(),
            silver::ExpKind::Call(callee, args) => {
                let func_id = self
                    .translator
                    .resolver
                    .resolve_member_id(callee)
                    .unwrap_or_else(|_| panic!("unknown function call target: {}", callee.0));
                let sig = self
                    .translator
                    .signatures
                    .resolve_function(func_id)
                    .unwrap_or_else(|_| panic!("missing function signature for {}", callee.0));
                let args = args
                    .iter()
                    .map(|a| self.translate_exp(a))
                    .collect::<Vec<_>>();
                self.emit_pure(
                    sig.ret.clone(),
                    PureInst::FunctionCall(vmir::FunctionCall {
                        func_id,
                        heap_ctx: self.current_heap.clone(),
                        args,
                    }),
                )
            }
            silver::ExpKind::Field(base, field) => {
                let field_id = self
                    .translator
                    .resolver
                    .resolve_member_id(field)
                    .unwrap_or_else(|_| panic!("unknown field access target: {}", field.0));
                let sig = self
                    .translator
                    .signatures
                    .resolve_function(field_id)
                    .unwrap_or_else(|_| panic!("missing field signature for {}", field.0));
                let base = self.translate_exp(base);
                self.emit_pure(
                    sig.ret.clone(),
                    PureInst::FunctionCall(vmir::FunctionCall {
                        func_id: field_id,
                        heap_ctx: self.current_heap.clone(),
                        args: vec![base],
                    }),
                )
            }
            silver::ExpKind::BinOp(silver::BinOp::Plus, l, r) => {
                let lv = self.translate_exp(l);
                let rv = self.translate_exp(r);
                self.emit_pure(Type::Int, PureInst::Binary(vmir::BinOp::Plus, lv, rv))
            }
            _ => unimplemented!("unsupported method expression: {exp:?}"),
        }
    }

    fn apply_resource(&mut self, resource_id: MemberId, args: Vec<Val>, mode: ContractMode) {
        let Declaration::Resource(resource) = self.translator.decls[resource_id]
            .as_ref()
            .unwrap_or_else(|| {
                panic!(
                    "resource not translated: {}",
                    self.translator.vmir_interner.resolve(&resource_id)
                )
            })
        else {
            panic!("expected resource declaration");
        };
        let (delta, cond) = self.materialize_resource(resource, &args);
        self.current_heap = match mode {
            ContractMode::AddAssume => {
                self.emit_heap(HeapInst::Add(self.current_heap.clone(), delta))
            }
            ContractMode::SubAssert => {
                self.emit_heap(HeapInst::Sub(self.current_heap.clone(), delta))
            }
        };
        match mode {
            ContractMode::AddAssume => self.insts.push(Inst::Assume(cond)),
            ContractMode::SubAssert => self.insts.push(Inst::Assert(cond)),
        }
    }

    fn materialize_resource(&mut self, resource: &Resource, args: &[Val]) -> (HeapVal, Val) {
        let param_count = resource.params.len();
        let mut val_map: HashMap<usize, Val> = HashMap::new();
        let mut heap_map: HashMap<usize, HeapVal> = HashMap::new();
        for (idx, arg) in args.iter().enumerate() {
            val_map.insert(idx, arg.clone());
        }

        for (inst_idx, inst) in resource.insts.iter().enumerate() {
            let old_idx = param_count + inst_idx;
            match inst {
                Inst::Pure(ty, pure) => {
                    let pure = substitute_pure(pure, &val_map, &heap_map);
                    let out = self.emit_pure(ty.clone(), pure);
                    val_map.insert(old_idx, out);
                }
                Inst::Heap(heap_inst) => {
                    let heap_inst = substitute_heap_inst(heap_inst, &val_map, &heap_map);
                    let out = self.emit_heap(heap_inst);
                    heap_map.insert(old_idx, out);
                }
                Inst::Assume(v) => self.insts.push(Inst::Assume(substitute_val(v, &val_map))),
                Inst::Assert(v) => self.insts.push(Inst::Assert(substitute_val(v, &val_map))),
                Inst::ResourceCall(call) => self.insts.push(Inst::ResourceCall(call.clone())),
            }
        }

        (
            substitute_heap(&resource.res.0, &heap_map),
            substitute_val(&resource.res.1, &val_map),
        )
    }
}

fn substitute_val(v: &Val, vals: &HashMap<usize, Val>) -> Val {
    match v {
        Val::Literal(l) => Val::Literal(l.clone()),
        Val::Temp(i) => vals.get(i).cloned().unwrap_or_else(|| Val::Temp(*i)),
    }
}

fn substitute_heap(h: &HeapVal, heaps: &HashMap<usize, HeapVal>) -> HeapVal {
    match h {
        HeapVal::Temp(i) => heaps.get(i).cloned().unwrap_or_else(|| HeapVal::Temp(*i)),
        HeapVal::Empty => HeapVal::Empty,
        HeapVal::Implicit => HeapVal::Implicit,
    }
}

fn substitute_pure(
    pure: &PureInst,
    vals: &HashMap<usize, Val>,
    heaps: &HashMap<usize, HeapVal>,
) -> PureInst {
    match pure {
        PureInst::Fresh => PureInst::Fresh,
        PureInst::Unary(op, v) => PureInst::Unary(*op, substitute_val(v, vals)),
        PureInst::Binary(op, l, r) => {
            PureInst::Binary(*op, substitute_val(l, vals), substitute_val(r, vals))
        }
        PureInst::Ternary(c, t, e) => PureInst::Ternary(
            substitute_val(c, vals),
            substitute_val(t, vals),
            substitute_val(e, vals),
        ),
        PureInst::Deref(h, loc) => {
            PureInst::Deref(substitute_heap(h, heaps), substitute_val(loc, vals))
        }
        PureInst::Perm(h, loc) => {
            PureInst::Perm(substitute_heap(h, heaps), substitute_val(loc, vals))
        }
        PureInst::FunctionCall(call) => PureInst::FunctionCall(vmir::FunctionCall {
            func_id: call.func_id,
            heap_ctx: substitute_heap(&call.heap_ctx, heaps),
            args: call.args.iter().map(|v| substitute_val(v, vals)).collect(),
        }),
        PureInst::HeapSubset(lhs, rhs) => {
            PureInst::HeapSubset(substitute_heap(lhs, heaps), substitute_heap(rhs, heaps))
        }
    }
}

fn substitute_heap_inst(
    heap: &HeapInst,
    vals: &HashMap<usize, Val>,
    heaps: &HashMap<usize, HeapVal>,
) -> HeapInst {
    match heap {
        HeapInst::Acc(acc) => HeapInst::Acc(vmir::Acc {
            loc: substitute_val(&acc.loc, vals),
            perm: substitute_val(&acc.perm, vals),
        }),
        HeapInst::Add(l, r) => HeapInst::Add(substitute_heap(l, heaps), substitute_heap(r, heaps)),
        HeapInst::Sub(l, r) => HeapInst::Sub(substitute_heap(l, heaps), substitute_heap(r, heaps)),
        HeapInst::Ternary(c, l, r) => HeapInst::Ternary(
            substitute_val(c, vals),
            substitute_heap(l, heaps),
            substitute_heap(r, heaps),
        ),
        HeapInst::Assign(h, v) => {
            HeapInst::Assign(substitute_heap(h, heaps), substitute_val(v, vals))
        }
    }
}

fn map_duplicate_error(err: DuplicateGlobalError) -> Vec<IdentifierError> {
    vec![IdentifierError::DuplicateName { name: err.0 }]
}

fn map_call_resolution_errors(errors: Vec<silver::CallResolutionError>) -> Vec<IdentifierError> {
    errors
        .into_iter()
        .map(|e| IdentifierError::CallResolution {
            message: e.to_string(),
        })
        .collect()
}

fn translate_type_with_resolver(resolver: &GlobalResolver, ty: &silver::Type) -> Type {
    match ty {
        silver::Type::Bool => Type::Bool,
        silver::Type::Int => Type::Int,
        silver::Type::Real => Type::Real,
        silver::Type::Ref => Type::Ref,
        silver::Type::Domain(idn, _) => Type::Domain(
            resolver
                .resolve_member_id(idn)
                .unwrap_or_else(|_| panic!("domain type not interned: {}", idn.0)),
        ),
    }
}
