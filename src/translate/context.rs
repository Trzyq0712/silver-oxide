//! `TranslationContext` — the read-only state every body-lowering helper
//! (`resource.rs`/`method.rs`/`pure_exp.rs`/`spatial.rs`) consumes. It **owns**
//! its maps (`name_map`, `contracts`, ...), built up progressively by the
//! coordinator (`mod.rs`) folding each `Translator::declare`'s `Meta` as
//! members are declared — it is a genuinely separate value from `Builder`
//! (the write side: `decls`/`vmir_interner`/`decl_names`/`groups`), not a
//! borrowed view of it. That separation is what lets a `Translator::define`
//! take `&TranslationContext` and `&mut impl Definer` (effectively `&mut
//! Builder`) in the same call without an aliasing conflict — the two values
//! share no lifetime.

use std::collections::HashMap;

use lasso::{Rodeo, Spur};

use crate::viper::{Interner, typed};
use crate::vmir;

/// ADT shape metadata recorded in `declare`, consumed when lowering `AdtCons` /
/// `AdtProj` / `AdtTag` use sites.
#[derive(Default)]
pub(crate) struct AdtInfo {
    /// A constructor's `Spur` to `(owning ADT `Spur`, tag index)`.
    pub ctor_tag: HashMap<Spur, (Spur, usize)>,
    /// A destructor's `Spur` to the `(adt id, variant, field)` it projects.
    pub dtor_sem: HashMap<Spur, (vmir::MemberId, usize, usize)>,
}

/// A member's contract ids (`#requires` / `#ensures`), absent when the member
/// omits that clause. For a **method** both are Resource ids. For a **function**
/// they are boolean Function ids, except a heap-dependent function's
/// `requires` (`heap_dep == true`), which is a self-framed Resource id — the
/// footprint whose snapshot the function takes as its trailing parameter.
#[derive(Default)]
pub(crate) struct MethodContracts {
    pub requires: Option<vmir::MemberId>,
    pub ensures: Option<vmir::MemberId>,
    /// Set only for functions whose `requires` grants permission (`acc`):
    /// call sites pass a `Snap` of the `requires` resource as an extra argument.
    pub heap_dep: bool,
}

/// A generic function's declared signature — the data needed to recover a call
/// site's type-argument instantiation. `ty_params` is the ordered list of
/// type-parameter names; `params`/`ret` are the declared types (possibly
/// mentioning those names as `Type::Generic`).
#[derive(Clone)]
pub(crate) struct GenericSig {
    pub ty_params: Vec<Spur>,
    pub params: Vec<typed::Type>,
    pub ret: typed::Type,
}

/// Read-only mid-translation state, owned and progressively folded by the
/// coordinator. Every body-lowering helper takes `&TranslationContext` — none
/// of them touch `Builder`'s write side (`decls`/`vmir_interner`/`decl_names`)
/// directly.
pub(crate) struct TranslationContext<'a> {
    pub interner: &'a Interner,
    /// Silver `Spur` names to VMIR `MemberId`s.
    pub name_map: HashMap<Spur, vmir::MemberId>,
    /// A field's `Spur` to its lowered value type (for `field@addr`'s `Addr<T>`).
    pub field_types: HashMap<Spur, vmir::Type>,
    /// A method's `Spur` to its contract resource ids.
    pub contracts: HashMap<Spur, MethodContracts>,
    /// ADT constructor/destructor metadata.
    pub adt: AdtInfo,
    /// A generic function's `Spur` to its declared generic signature.
    pub fn_generic_sigs: HashMap<Spur, GenericSig>,
    /// Location **group** tags (`Type::Addr.group`) — field/predicate names.
    /// A clone of `Builder`'s `groups` interner, taken once `declare`
    /// finishes (fields/predicates are the only ones that register groups,
    /// all during `declare`; nothing registers one afterwards).
    pub(crate) groups: Rodeo<Spur>,
    /// Type parameters of the **generic body currently being lowered** (a
    /// domain axiom's used generics), so `lower_type`/`call_type_args` map a
    /// `typed::Type::Generic` to its positional `vmir::Type::Generic(i)`.
    /// Scoped by `DomainTranslator::define` (set per axiom, cleared after);
    /// empty everywhere else — method/function/resource bodies are monomorphic.
    pub(crate) decl_generics: Vec<Spur>,
}

impl<'a> TranslationContext<'a> {
    pub(crate) fn new(interner: &'a Interner) -> Self {
        Self {
            interner,
            name_map: HashMap::new(),
            field_types: HashMap::new(),
            contracts: HashMap::new(),
            adt: AdtInfo::default(),
            fn_generic_sigs: HashMap::new(),
            groups: Rodeo::new(),
            decl_generics: Vec::new(),
        }
    }

    /// A call's full type-argument instantiation, in the callee's own
    /// type-parameter order, recovered by matching the callee's declared
    /// generic signature against the concrete argument and result types. Empty
    /// for a monomorphic callee (no registered generic signature). This is the
    /// inference the backend would otherwise have to redo: doing it once here
    /// lets the verifier read the instantiation verbatim.
    pub(crate) fn call_type_args(
        &self,
        name: Spur,
        arg_tys: &[&typed::Type],
        ret_ty: &typed::Type,
    ) -> Vec<vmir::Type> {
        let Some(sig) = self.fn_generic_sigs.get(&name) else {
            return Vec::new();
        };
        let mut subst: HashMap<Spur, typed::Type> = HashMap::new();
        for (decl, actual) in sig.params.iter().zip(arg_tys) {
            super::match_generic(decl, actual, &mut subst);
        }
        super::match_generic(&sig.ret, ret_ty, &mut subst);
        // Every type parameter is guaranteed to occur in the params/ret (a
        // parameter used only in the body is not a real type parameter), so the
        // match populates all of them.
        sig.ty_params
            .iter()
            .map(|n| {
                let t = subst
                    .get(n)
                    .expect("type parameter must occur in params/ret");
                self.lower_type(t)
            })
            .collect()
    }

    /// The `#requires` contract resource of method `m`, if it has one.
    pub(crate) fn method_requires(&self, m: Spur) -> Option<vmir::MemberId> {
        self.contracts.get(&m).and_then(|c| c.requires)
    }

    /// The `#ensures` contract resource of method `m`, if it has one.
    pub(crate) fn method_ensures(&self, m: Spur) -> Option<vmir::MemberId> {
        self.contracts.get(&m).and_then(|c| c.ensures)
    }

    /// Lower a type against the current body's type parameters
    /// (`decl_generics` — empty outside generic bodies, i.e. everywhere but a
    /// domain axiom). For ADT-declaration field types (which may mention type
    /// parameters) call the free [`super::lower_type`] with the owning ADT's
    /// parameter list instead.
    pub(crate) fn lower_type(&self, ty: &typed::Type) -> vmir::Type {
        super::lower_type(&self.name_map, &self.decl_generics, ty)
    }

    /// The interned group tag for a field/predicate name (registered in the
    /// declare phase).
    pub fn group_tag(&self, name: Spur) -> Spur {
        let s = self.interner.resolve(&name);
        self.groups
            .get(s)
            .unwrap_or_else(|| panic!("group tag `{s}` not registered"))
    }
}
