use crate::{
    silver,
    translate::pure_exp::{PureExpBackend, PureExpTranslator},
    vmir,
};

pub trait HeapExpBackend: PureExpBackend {
    fn emit_heap(&mut self, heap: vmir::HeapInst) -> vmir::HeapVal;
}

/// In Inhale mode, the translator immediately adds the heap chunks
/// to the heap provided via [heap_ctx] and evaluates any pure expressions
/// in the newly produced heap.
///
/// In Exhale mode, the translator collects the heap chunks into a separate
/// heap delta and evaluates all pure expressions in the original [heap_ctx].
/// Only at the end the heap delta is subtracted from the input heap.
pub struct HeapExpTranslator<'a, B: HeapExpBackend> {
    pub backend: &'a mut B,
    pub pc: Option<vmir::Val>,
    pub mode: HeapMode,
    pub heap_ctx: vmir::HeapVal,
}

pub enum HeapMode {
    Inhale,
    Exhale,
}

impl<'a, B: HeapExpBackend> HeapExpTranslator<'a, B> {
    pub fn translate(mut self, exp: &silver::HeapExp) -> (vmir::HeapVal, vmir::Val) {
        let (heap, cond) = match self.mode {
            HeapMode::Inhale => self.translate_heap(self.heap_ctx, &exp.kind),
            HeapMode::Exhale => {
                let (heap_delta, cond) = self.translate_heap(vmir::HeapVal::Empty, &exp.kind);
                // To perform the heap subtraction, first need to check it is safe to do
                // under the current path condition.
                let check = self
                    .backend
                    .emit_pure(vmir::PureInst::HeapSubset(heap_delta, self.heap_ctx));
                self.assert(check);
                let final_heap = self
                    .backend
                    .emit_heap(vmir::HeapInst::Sub(self.heap_ctx, heap_delta));
                (final_heap, cond)
            }
        };
        (heap, cond.unwrap_or(vmir::TRUE))
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

    fn translate_pure(&mut self, exp: &silver::PureExp) -> vmir::Val {
        let mut pure = PureExpTranslator {
            backend: self.backend,
            pc: self.pc.clone(),
            heap: self.heap_ctx,
        };
        pure.translate(exp).unwrap()
    }

    fn translate_acc(
        &mut self,
        input_heap: vmir::HeapVal,
        acc: &silver::AccExp,
    ) -> (vmir::HeapVal, Option<vmir::Val>) {
        let loc = self.translate_pure(&acc.acc.loc);
        let perm = self.translate_pure(&acc.perm);
        let acc = self
            .backend
            .emit_heap(vmir::HeapInst::Acc(vmir::Acc { loc, perm }));
        let new_heap = self.backend.emit_heap(vmir::HeapInst::Add(input_heap, acc));
        (new_heap, None)
    }

    fn translate_conj(
        &mut self,
        input_heap: vmir::HeapVal,
        parts: &[silver::HeapExp],
    ) -> (vmir::HeapVal, Option<vmir::Val>) {
        let mut cur_heap = input_heap;
        let mut cur_cond: Option<vmir::Val> = None;
        for part in parts {
            let (next_heap, next_cond) = self.translate_heap(cur_heap, &part.kind);
            cur_heap = next_heap;
            cur_cond = match (cur_cond, next_cond) {
                (Some(l), Some(r)) => Some(self.backend.emit_pure(vmir::PureInst::Ternary(
                    l,
                    r,
                    vmir::FALSE,
                ))),
                (Some(c), None) | (None, Some(c)) => Some(c),
                (None, None) => None,
            };
        }
        (cur_heap, cur_cond)
    }

    fn translate_heap(
        &mut self,
        input_heap: vmir::HeapVal,
        exp: &silver::HeapExpKind,
    ) -> (vmir::HeapVal, Option<vmir::Val>) {
        let (new_heap, val) = match exp {
            silver::HeapExpKind::Pure(exp) => self.translate_pure_heap(input_heap, exp.as_ref()),
            silver::HeapExpKind::Acc(acc) => self.translate_acc(input_heap, acc),
            silver::HeapExpKind::Conjunction(parts) => self.translate_conj(input_heap, parts),
            silver::HeapExpKind::Ternary(..) => unimplemented!("Need to support path conditions"),
            _ => unimplemented!(),
        };
        if let HeapMode::Inhale = self.mode {
            self.heap_ctx = new_heap;
        }
        (new_heap, val)
    }

    fn translate_pure_heap(
        &mut self,
        input_heap: vmir::HeapVal,
        exp: &silver::ExpKind,
    ) -> (vmir::HeapVal, Option<vmir::Val>) {
        match exp {
            silver::ExpKind::BinOp(silver::BinOp::And, left, right) => {
                let (heap_l, cond_l) = self.translate_pure_heap(input_heap, left.as_ref());
                let (heap_r, cond_r) = self.translate_pure_heap(heap_l, right.as_ref());
                let cond = match (cond_l, cond_r) {
                    (Some(l), Some(r)) => Some(self.backend.emit_pure(vmir::PureInst::Ternary(
                        l,
                        r,
                        vmir::FALSE,
                    ))),
                    (Some(c), None) | (None, Some(c)) => Some(c),
                    (None, None) => None,
                };
                (heap_r, cond)
            }
            silver::ExpKind::Call(..) => {
                let loc = self.translate_pure(&Box::new(exp.clone()));
                let acc = self.backend.emit_heap(vmir::HeapInst::Acc(vmir::Acc {
                    loc,
                    perm: vmir::write(),
                }));
                (
                    self.backend.emit_heap(vmir::HeapInst::Add(input_heap, acc)),
                    None,
                )
            }
            _ => (
                input_heap,
                Some(self.translate_pure(&Box::new(exp.clone()))),
            ),
        }
    }
}
