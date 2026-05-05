use std::collections::HashMap;

use crate::{
    silver,
    translate::{
        heap_exp::{HeapExpBackend, HeapExpTranslator, HeapMode},
        inst::UntypedInst,
        pure_exp::PureExpBackend,
        VmirTc,
    },
    vmir,
};

pub struct ResourceBuilder<'sil> {
    tc: VmirTc,
    insts: Vec<UntypedInst>,
    param_map: HashMap<&'sil silver::Ident, vmir::Val>,
    heaps: HashMap<&'sil silver::Ident, vmir::HeapVal>,
    pure_ctr: usize,
    heap_ctr: usize,
}

impl<'sil> PureExpBackend for ResourceBuilder<'sil> {
    fn resolve_var(&self, ident: &silver::Ident) -> Result<vmir::Val, ()> {
        self.param_map.get(ident).cloned().ok_or(())
    }

    fn emit_pure(&mut self, pure: vmir::PureInst) -> vmir::Val {
        self.insts.push(UntypedInst::Pure(pure));
        let res = vmir::Val::Temp(self.pure_ctr);
        self.pure_ctr += 1;
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

    fn resolve_name(&self, ident: &silver::Ident) -> Result<vmir::MemberId, ()> {
        todo!()
    }
}

impl<'sil> HeapExpBackend for ResourceBuilder<'sil> {
    fn emit_heap(&mut self, heap_inst: vmir::HeapInst) -> vmir::HeapVal {
        self.insts.push(UntypedInst::Heap(heap_inst));
        let res = vmir::HeapVal::Temp(self.heap_ctr);
        self.heap_ctr += 1;
        res
    }
}

impl<'sil> ResourceBuilder<'sil> {
    pub fn build(mut self, exp: &silver::HeapExp) -> Result<vmir::Resource, ()> {
        let translator = HeapExpTranslator {
            backend: &mut self,
            pc: None,
            mode: HeapMode::Inhale,
            heap_ctx: vmir::HeapVal::Empty,
        };
        todo!()
    }
}
