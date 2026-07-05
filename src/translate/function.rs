//! Lower a Silver `function` to its `vmir::Function` (+ `#requires`/`#ensures`
//! contracts). See [`FunctionTranslator::define`] for the heap-free vs.
//! heap-dependent split.

use std::collections::HashMap;

use lasso::Spur;

use crate::translate::hole::{Declarator, Definer, Hole};
use crate::translate::{TranslationContext, TranslationError, pure_exp, spatial};
use crate::viper::{Interner, typed};
use crate::vmir;

/// Metadata the coordinator folds into `TranslationContext` (`contracts`,
/// `name_map`) once a function is declared.
#[derive(Debug)]
pub(crate) struct FunctionMeta {
    pub silver_name: Spur,
    pub function: vmir::MemberId,
    pub requires: Option<vmir::MemberId>,
    pub ensures: Option<vmir::MemberId>,
    /// Set when `requires` contains an `acc` — the function's `#requires`
    /// slot is a self-framed `Resource` (not a boolean function), and call
    /// sites pass its snapshot as an extra argument.
    pub heap_dep: bool,
}

/// A function's `#requires` slot is a boolean [`vmir::Function`] when
/// heap-free, or a self-framed [`vmir::Resource`] (footprint + bool) when the
/// precondition grants permission (`heap_dep`, decided at declare time via
/// [`spatial::spatial_contains_acc`]).
pub(crate) enum RequiresHole {
    HeapFree(Hole<vmir::Function>),
    HeapDep(Hole<vmir::Resource>),
}

impl RequiresHole {
    fn abandon(self) {
        match self {
            RequiresHole::HeapFree(h) => h.abandon(),
            RequiresHole::HeapDep(h) => h.abandon(),
        }
    }
}

pub(crate) struct FunctionTranslator {
    fn_hole: Hole<vmir::Function>,
    requires_hole: Option<RequiresHole>,
    ensures_hole: Option<Hole<vmir::Function>>,
    meta: FunctionMeta,
}

impl FunctionTranslator {
    pub(crate) fn declare(
        f: &typed::Function,
        interner: &Interner,
        declarator: &mut impl Declarator,
    ) -> Self {
        let name = interner.resolve(&f.name.0).to_string();
        let (fn_id, fn_hole) = declarator.allocate_hole::<vmir::Function>(&name);

        let mut requires = None;
        let mut requires_hole = None;
        let mut heap_dep = false;
        if let Some(req_exp) = &f.requires {
            // An `acc` in the precondition makes the function heap-dependent:
            // its `#requires` slot is filled with a Resource (not a boolean
            // Function), and call sites pass its snapshot as an extra
            // argument. Recorded here so call sites lowered before this
            // function's `define` see it (via the folded `Meta`).
            heap_dep = spatial::spatial_contains_acc(req_exp);
            let req_name = format!("{name}#requires");
            if heap_dep {
                let (id, hole) = declarator.allocate_hole::<vmir::Resource>(&req_name);
                requires = Some(id);
                requires_hole = Some(RequiresHole::HeapDep(hole));
            } else {
                let (id, hole) = declarator.allocate_hole::<vmir::Function>(&req_name);
                requires = Some(id);
                requires_hole = Some(RequiresHole::HeapFree(hole));
            }
        }

        let mut ensures = None;
        let mut ensures_hole = None;
        if f.ensures.is_some() {
            let (id, hole) = declarator.allocate_hole::<vmir::Function>(&format!("{name}#ensures"));
            ensures = Some(id);
            ensures_hole = Some(hole);
        }

        FunctionTranslator {
            fn_hole,
            requires_hole,
            ensures_hole,
            meta: FunctionMeta {
                silver_name: f.name.0,
                function: fn_id,
                requires,
                ensures,
                heap_dep,
            },
        }
    }

    pub(crate) fn meta(&self) -> &FunctionMeta {
        &self.meta
    }

    /// Abandon every `Hole` this translator still owns — called on an error
    /// path so the drop bomb doesn't panic on top of the `TranslationError`
    /// being propagated.
    fn abandon(
        fn_hole: Option<Hole<vmir::Function>>,
        requires_hole: Option<RequiresHole>,
        ensures_hole: Option<Hole<vmir::Function>>,
    ) {
        if let Some(h) = fn_hole {
            h.abandon();
        }
        if let Some(h) = requires_hole {
            h.abandon();
        }
        if let Some(h) = ensures_hole {
            h.abandon();
        }
    }

    /// Fill this function's reserved slots (see [`Self::declare`]): the main
    /// function decl, plus `#requires` / `#ensures` contracts when present.
    ///
    /// Functions are **pure and heap-free** in VMIR. A **heap-free** function
    /// (no `acc` in its `requires`) gets boolean contract functions stitched
    /// as pure `assume`/`assert`:
    /// - `#requires` → a boolean [`vmir::Function`] `params -> Bool`.
    /// - `#ensures` → a boolean [`vmir::Function`] `(params ++ result) -> Bool`.
    /// - the main function → its lowered body (when present) which
    ///   **assumes** `#requires(params)` at entry and **asserts**
    ///   `#ensures(params, result)` at exit.
    ///
    /// A **heap-dependent** function (`acc` in its `requires`) instead
    /// receives its precondition **snapshot** as a trailing parameter:
    /// - `#requires` → a self-framed [`vmir::Resource`] (footprint + bool);
    ///   its pure conjuncts live in the resource bool, so there is no separate
    ///   boolean requires-function.
    /// - `#ensures` → a boolean [`vmir::Function`]
    ///   `(params ++ [result, s: Snap(req)]) -> Bool` whose body reconstructs
    ///   the precondition heap from `s` (`FromSnap`) and reads it.
    /// - the main function → `(params ++ [s: Snap(req)]) -> ret`; its body
    ///   opens with the same `FromSnap` (which implicitly assumes the
    ///   resource bool — no entry `assume`) and asserts
    ///   `#ensures(params, result, s)` at exit. Call sites build `s` with
    ///   `PureInst::Snap` (which implicitly asserts the precondition) — see
    ///   `pure_exp::lower_func_app`.
    pub(crate) fn define(
        self,
        ctx: &TranslationContext<'_>,
        f: &typed::Function,
        definer: &mut impl Definer,
    ) -> Result<(), TranslationError> {
        let FunctionTranslator {
            fn_hole,
            requires_hole,
            ensures_hole,
            meta,
        } = self;
        let mut fn_hole = Some(fn_hole);
        let mut requires_hole = requires_hole;
        let mut ensures_hole = ensures_hole;

        let fname = ctx.interner.resolve(&meta.silver_name).to_string();
        let n_params = f.params.len();
        let params: Vec<vmir::Type> = f.params.iter().map(|p| ctx.lower_type(&p.ty)).collect();
        let ret = ctx.lower_type(&f.ret);
        let heap_dep = meta.heap_dep;

        // Params occupy `Val::Temp(0..n_params)` in every body lowered below.
        let mut env: HashMap<Spur, vmir::Val> = HashMap::new();
        for (i, p) in f.params.iter().enumerate() {
            env.insert(p.name.0, vmir::Val::Temp(i));
        }

        // #requires: heap-free → a boolean function `params -> Bool`;
        // heap-dependent → a self-framed Resource (footprint + bool).
        if let Some(requires) = f.requires.as_ref() {
            let name = definer.intern_name(&format!("{fname}#requires"));
            match requires_hole.take().expect("declared when f.requires is Some") {
                RequiresHole::HeapDep(hole) => {
                    let body = match spatial::lower_spatial_never(
                        ctx,
                        &env,
                        requires,
                        n_params,
                        vmir::HeapVal::Empty,
                        0,
                    ) {
                        Ok(b) => b,
                        Err(e) => {
                            hole.abandon();
                            Self::abandon(fn_hole.take(), None, ensures_hole.take());
                            return Err(e);
                        }
                    };
                    definer.define_resource(
                        hole,
                        vmir::Resource {
                            name,
                            params: params.clone(),
                            precond: vmir::Precond::SelfFramed,
                            body: Some(body),
                        },
                    );
                }
                RequiresHole::HeapFree(hole) => {
                    let body =
                        match spatial::lower_pure_precond_body(ctx, &env, requires, n_params) {
                            Ok(b) => b,
                            Err(e) => {
                                hole.abandon();
                                Self::abandon(fn_hole.take(), None, ensures_hole.take());
                                return Err(e);
                            }
                        };
                    definer.define_function(
                        hole,
                        vmir::Function {
                            name,
                            ty_params: 0.into(),
                            params: params.clone().into(),
                            ret: vmir::Type::Bool,
                            body: Some(body),
                        },
                    );
                }
            }
        }

        // The trailing snapshot parameter of a heap-dependent function (and of
        // its ensures function, where it sits after `result`).
        let snap_ty = heap_dep.then(|| {
            let req_id = meta.requires.expect("heap-dep implies a requires");
            vmir::Type::Snap(req_id)
        });
        let param_vals: Vec<vmir::Val> = (0..n_params).map(vmir::Val::Temp).collect();

        // #ensures: a boolean function `(params ++ result) -> Bool`, with the
        // snapshot appended for a heap-dependent function. `result` occupies
        // `Val::Temp(n_params)`, the snapshot (if any) `Temp(n_params + 1)`;
        // body temps start after them.
        if let Some(ensures) = &f.ensures {
            let hole = ensures_hole.take().expect("declared when f.ensures is Some");
            let mut ens_params = params.clone();
            ens_params.push(ret.clone());
            let result = vmir::Val::Temp(n_params);
            let mut val_base = n_params + 1;
            let mut snap_entry = None;
            if let Some(snap_ty) = &snap_ty {
                ens_params.push(snap_ty.clone());
                let vmir::Type::Snap(req_id) = snap_ty else {
                    unreachable!()
                };
                snap_entry = Some(pure_exp::SnapEntry {
                    resource: *req_id,
                    args: param_vals.clone(),
                    snap: vmir::Val::Temp(val_base),
                });
                val_base += 1;
            }
            let body = match pure_exp::lower_function_body(
                ctx,
                &env,
                ensures,
                val_base,
                vmir::HeapVal::Empty,
                Some(result),
                None,
                snap_entry,
            ) {
                Ok(b) => b,
                Err(e) => {
                    hole.abandon();
                    Self::abandon(fn_hole.take(), None, None);
                    return Err(e);
                }
            };
            let name = definer.intern_name(&format!("{fname}#ensures"));
            definer.define_function(
                hole,
                vmir::Function {
                    name,
                    ty_params: 0.into(),
                    params: ens_params.into(),
                    ret: vmir::Type::Bool,
                    body: Some(body),
                },
            );
        }

        // The main function: pure and heap-free at the call boundary. Its body
        // (when present) assumes the precondition at entry — as a pure
        // `assume #requires(params)` when heap-free, or implicitly via the
        // `FromSnap` heap reconstruction when heap-dependent — and asserts
        // `#ensures(params, result[, s])` at exit.
        let mut fn_params = params;
        let mut val_base = n_params;
        let mut snap_entry = None;
        let mut contract_snap = None;
        if let Some(snap_ty) = &snap_ty {
            fn_params.push(snap_ty.clone());
            let vmir::Type::Snap(req_id) = snap_ty else {
                unreachable!()
            };
            let snap_val = vmir::Val::Temp(n_params);
            snap_entry = Some(pure_exp::SnapEntry {
                resource: *req_id,
                args: param_vals.clone(),
                snap: snap_val.clone(),
            });
            contract_snap = Some(snap_val);
            val_base += 1;
        }
        let contract = pure_exp::FnContract {
            // Heap-dependent: the precondition is assumed by `FromSnap`, not
            // by a boolean entry stitch.
            requires: if heap_dep { None } else { meta.requires },
            ensures: meta.ensures,
            params: param_vals,
            snap: contract_snap,
        };
        let fn_hole = fn_hole.take().expect("not yet consumed");
        let body = match &f.body {
            None => None,
            Some(body_exp) => match pure_exp::lower_function_body(
                ctx,
                &env,
                body_exp,
                val_base,
                vmir::HeapVal::Empty,
                None,
                Some(contract),
                snap_entry,
            ) {
                Ok(b) => Some(b),
                Err(e) => {
                    fn_hole.abandon();
                    return Err(e);
                }
            },
        };
        let name = definer.intern_name(&fname);
        definer.define_function(
            fn_hole,
            vmir::Function {
                name,
                ty_params: 0.into(),
                params: fn_params.into(),
                ret,
                body,
            },
        );
        Ok(())
    }
}
