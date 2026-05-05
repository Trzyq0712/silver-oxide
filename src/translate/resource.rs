use crate::translate::global_resolver::GlobalResolver;
use crate::translate::heap_exp::{HeapExpBackend, HeapExpTranslator, HeapMode};
use crate::translate::inst::UntypedInst;
use crate::translate::pure_exp::PureExpBackend;
use crate::translate::{typecheck::TcType, VmirTc, VmirTranslator};
use crate::{silver, vmir, HashMap};
use rusttyc::TcKey;

pub struct MethodContractResources {
    pub requires: Option<(vmir::MemberId, vmir::Resource)>,
    pub ensures: Option<(vmir::MemberId, vmir::Resource)>,
}

pub fn translate_method_contracts(
    translator: &VmirTranslator,
    method_id: vmir::MemberId,
    method: &silver::Method,
) -> MethodContractResources {
    let resolved_method = translator.resolver.resolve_method_id(method_id).unwrap();
    let arg_bindings = method
        .signature
        .args
        .iter()
        .enumerate()
        .filter_map(|(idx, arg)| {
            arg.idn()
                .map(|idn| (idn.0.clone(), resolved_method.args[idx].clone()))
        })
        .collect::<Vec<_>>();
    let mut requires = None;
    if let (Some(req_id), Some(pre)) = (
        resolved_method.precond,
        method.contract.precondition.as_ref(),
    ) {
        let builder = ResourceBuilder::new(translator.resolver.clone(), arg_bindings.clone(), None);
        let res = builder.build(pre).unwrap();
        requires = Some((req_id, res));
    }

    let mut ensures = None;
    if let (Some(ens_id), Some(post)) = (
        resolved_method.postcond,
        method.contract.postcondition.as_ref(),
    ) {
        let mut params = arg_bindings.clone();
        params.extend(
            method
                .signature
                .ret
                .iter()
                .enumerate()
                .filter_map(|(idx, ret)| {
                    ret.idn()
                        .map(|idn| (idn.0.clone(), resolved_method.ret[idx].clone()))
                }),
        );
        let pre_dep = resolved_method
            .precond
            .map(|req_id| (req_id, resolved_method.args.len()));
        let builder = ResourceBuilder::new(translator.resolver.clone(), params, pre_dep);
        let res = builder.build(post).unwrap();
        ensures = Some((ens_id, res));
    }

    MethodContractResources { requires, ensures }
}

pub struct ResourceBuilder {
    resolver: GlobalResolver,
    params: Vec<vmir::Type>,
    tc: VmirTc,
    insts: Vec<UntypedInst>,
    param_map: HashMap<silver::Ident, vmir::Val>,
    next_temp: usize,
    precond: Option<(vmir::MemberId, usize)>,
}

impl PureExpBackend for ResourceBuilder {
    fn resolve_var(&self, ident: &silver::Ident) -> Result<vmir::Val, ()> {
        self.param_map.get(ident).cloned().ok_or(())
    }

    fn emit_pure(&mut self, pure: vmir::PureInst) -> vmir::Val {
        let res = vmir::Val::Temp(self.next_temp);
        self.next_temp += 1;
        self.insts.push(UntypedInst::Pure(pure));
        res
    }

    fn emit_assert(&mut self, check: vmir::Val) {
        self.insts.push(UntypedInst::Assert(check));
    }

    fn tc_mut(&mut self) -> &mut VmirTc {
        &mut self.tc
    }

    fn old_heap(&self, label: Option<&silver::Ident>) -> Result<vmir::HeapVal, ()> {
        match label {
            Some(_) => Err(()),
            None => Ok(vmir::HeapVal::Implicit),
        }
    }

    fn resolve_global(&self, ident: &silver::Ident) -> Result<vmir::MemberId, ()> {
        if let Ok(function) = self.resolver.resolve_function(ident) {
            return Ok(function.id);
        }
        if let Ok(field) = self.resolver.resolve_field(ident) {
            return Ok(field.id);
        }
        Err(())
    }
}

impl HeapExpBackend for ResourceBuilder {
    fn emit_heap(&mut self, heap_inst: vmir::HeapInst) -> vmir::HeapVal {
        let res = vmir::HeapVal::Temp(self.next_temp);
        self.next_temp += 1;
        self.insts.push(UntypedInst::Heap(heap_inst));
        res
    }
}

impl ResourceBuilder {
    pub fn new(
        resolver: GlobalResolver,
        params: Vec<(silver::Ident, vmir::Type)>,
        precond: Option<(vmir::MemberId, usize)>,
    ) -> Self {
        let mut tc = VmirTc::new();
        let mut param_map = HashMap::new();
        let mut param_types = Vec::with_capacity(params.len());
        for (idx, (ident, ty)) in params.iter().enumerate() {
            let val = vmir::Val::Temp(idx);
            param_map.insert(ident.clone(), val.clone());
            let key = tc.get_var_key(&val);
            impose_type_recursive(&mut tc, key, ty).unwrap();
            param_types.push(ty.clone());
        }
        Self {
            resolver,
            params: param_types.clone(),
            tc,
            insts: Vec::new(),
            param_map,
            next_temp: param_types.len(),
            precond,
        }
    }

    pub fn build(mut self, exp: &silver::HeapExp) -> Result<vmir::Resource, ()> {
        let translator = HeapExpTranslator {
            backend: &mut self,
            pc: None,
            mode: HeapMode::Inhale,
            heap_ctx: vmir::HeapVal::Empty,
        };
        let (heap, cond) = translator.translate(exp);
        let type_table = self.tc.clone().type_check().map_err(|_| ())?;

        let mut typed_insts = Vec::with_capacity(self.insts.len());
        let param_count = self.params.len();
        for (inst_idx, inst) in self.insts.into_iter().enumerate() {
            match inst {
                UntypedInst::Pure(pure) => {
                    let out_idx = param_count + inst_idx;
                    let out_key = self.tc.get_var_key(&vmir::Val::Temp(out_idx));
                    let ty = type_table
                        .get(&out_key)
                        .cloned()
                        .unwrap_or(vmir::Type::Bool);
                    typed_insts.push(vmir::Inst::Pure(ty, pure));
                }
                UntypedInst::Assume(v) => typed_insts.push(vmir::Inst::Assume(v)),
                UntypedInst::Assert(v) => typed_insts.push(vmir::Inst::Assert(v)),
                UntypedInst::ResourceCall(call) => typed_insts.push(vmir::Inst::ResourceCall(call)),
                UntypedInst::Heap(h) => typed_insts.push(vmir::Inst::Heap(h)),
            }
        }

        let requires = self.precond.map(|(id, arg_count)| {
            let args = (0..arg_count).map(vmir::Val::Temp).collect();
            (id, args)
        });

        Ok(vmir::Resource {
            params: self.params,
            requires,
            insts: typed_insts,
            res: (heap, cond),
        })
    }
}

fn impose_type_recursive(tc: &mut VmirTc, key: TcKey, ty: &vmir::Type) -> Result<(), ()> {
    tc.impose(key.concretizes_explicit(TcType::from(ty)))
        .map_err(|_| ())?;
    if let vmir::Type::Addr(inner) = ty {
        let child = tc.get_child_key(key, 0).map_err(|_| ())?;
        impose_type_recursive(tc, child, inner)?;
    }
    Ok(())
}
