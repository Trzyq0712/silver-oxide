//! The **write side** of translation: [`Builder`], which owns the growing
//! `vmir::Program`, and the [`DeclSlot`] capability it hands out to reserve and
//! later fill each declaration. `Builder` implements the [`Declarator`] /
//! [`Definer`] interfaces the translators drive.
//!
//! `Builder` and `DeclSlot` live in the *same* module on purpose — that
//! co-location is what makes the capability sound (see below), so they cannot
//! be split apart.
//!
//! ## `DeclSlot` — an unforgeable, affine write capability
//!
//! A [`DeclSlot<T>`] is a write-capability token for exactly one declaration
//! slot, tagged with the payload type `T` it will hold. It is `#[must_use]`,
//! non-`Clone`, and consumed by value: `Definer::define_*` takes a
//! `DeclSlot<T>` by move, so a slot can be filled **at most once** (a second
//! fill is a move error). That every reserved slot is filled **at least once**
//! is checked in one place — [`Builder::finalize`], which panics (naming the
//! member) on any slot left empty. On a translation *error* an unfilled slot is
//! simply dropped and the whole `Builder` discarded, so no per-slot cleanup is
//! needed.
//!
//! **Unforgeable.** `DeclSlot::new` and `DeclSlot::fill` are private to *this*
//! module, and `Builder` (the only `Declarator`/`Definer` impl) lives here too.
//! The translator submodules (`decl::field`, `decl::adt`, …) are *not*
//! descendants of this module, so they cannot reach the private constructor or
//! filler: a translator can only receive a slot and hand it to `define_*` — it
//! can neither fabricate nor fill one. This makes `Builder::alloc_slot` the
//! single source of every slot.

use std::marker::PhantomData;

use lasso::{Rodeo, Spur};
use typed_index_collections::TiVec;

use crate::vmir;

/// A write-capability token for the declaration slot `id`. `T` is the `vmir`
/// declaration payload type the slot will hold (`vmir::Function`,
/// `vmir::Resource`, `vmir::Method`, `vmir::Adt`, `vmir::Domain`) — a phantom
/// marker only, never constructed.
#[must_use = "a DeclSlot must be handed to a Definer::define_* to fill its member"]
pub(crate) struct DeclSlot<T> {
    id: vmir::MemberId,
    _marker: PhantomData<T>,
}

impl<T> DeclSlot<T> {
    /// Mint a fresh slot for `id`. **Private to `builder`** — only
    /// [`Builder::alloc_slot`] calls it, which is what makes a slot unforgeable
    /// outside this module.
    fn new(id: vmir::MemberId) -> Self {
        Self {
            id,
            _marker: PhantomData,
        }
    }

    /// Consume the slot, handing back its id so the `Definer` impl can write the
    /// actual `Declaration` there. By-value, so a slot fills at most once.
    /// **Private to `builder`** — only `Builder`'s `Definer` impl fills a slot.
    fn fill(self) -> vmir::MemberId {
        self.id
    }
}

/// Reserves declaration slots. The sole impl is [`Builder`]; an external impl
/// could not satisfy it, since constructing a `DeclSlot` requires the
/// module-private `DeclSlot::new`.
pub(crate) trait Declarator {
    fn alloc_slot<T>(&mut self, name: &str) -> (vmir::MemberId, DeclSlot<T>);

    /// Register a field/predicate name as a location **group** tag
    /// (`Type::Addr.group`), interned separately from `Declaration` names.
    fn intern_group(&mut self, s: &str) -> Spur;
}

/// Fills declaration slots, one method per `vmir` payload kind, each consuming
/// the matching `DeclSlot<T>` by value. Also exposes the mid-`define` string
/// interning `declare`-time helpers don't need. Only [`Builder`] can fill a
/// slot (see `DeclSlot::fill`).
pub(crate) trait Definer {
    fn define_function(&mut self, slot: DeclSlot<vmir::Function>, decl: vmir::Function);
    fn define_resource(&mut self, slot: DeclSlot<vmir::Resource>, decl: vmir::Resource);
    fn define_method(&mut self, slot: DeclSlot<vmir::Method>, decl: vmir::Method);
    fn define_adt(&mut self, slot: DeclSlot<vmir::Adt>, decl: vmir::Adt);
    fn define_domain(&mut self, slot: DeclSlot<vmir::Domain>, decl: vmir::Domain);
    fn define_axiom(&mut self, slot: DeclSlot<vmir::Axiom>, decl: vmir::Axiom);
    fn define_quantifier(&mut self, slot: DeclSlot<vmir::Quantifier>, decl: vmir::Quantifier);

    fn intern_name(&mut self, s: &str) -> Spur;
}

/// Reserve `n` quantifier occurrence slots named `{base}#quant{j}` — one per
/// `forall` counted in the hosting declaration (nested included), in the
/// preorder its lowerings will consume them.
pub(crate) fn alloc_quant_slots(
    d: &mut impl Declarator,
    base: &str,
    n: usize,
) -> Vec<(vmir::MemberId, DeclSlot<vmir::Quantifier>)> {
    (0..n)
        .map(|j| d.alloc_slot::<vmir::Quantifier>(&format!("{base}#quant{j}")))
        .collect()
}

/// Fill each pre-allocated quantifier slot with its built declaration. Built
/// order is innermost-first (an inner `forall` finishes lowering before its
/// encloser pushes), so slots are matched by occurrence id, not position. Each
/// quantifier's name is set to match its slot registration `{base}#quant{j}`.
pub(crate) fn fill_quant_slots(
    definer: &mut impl Definer,
    base: &str,
    slots: Vec<(vmir::MemberId, DeclSlot<vmir::Quantifier>)>,
    built: Vec<(vmir::MemberId, vmir::Quantifier)>,
) {
    debug_assert_eq!(slots.len(), built.len());
    let mut by_id: std::collections::HashMap<vmir::MemberId, vmir::Quantifier> =
        built.into_iter().collect();
    for (j, (slot_id, qslot)) in slots.into_iter().enumerate() {
        let mut quant = by_id.remove(&slot_id).expect("forall slot never filled");
        quant.name = definer.intern_name(&format!("{base}#quant{j}"));
        definer.define_quantifier(qslot, quant);
    }
}

/// Occurrence-id budget plus built-quantifier collector for one hosting
/// declaration, threaded (in counting order) through each of its body/contract
/// lowerings — every internal `Sink` seeds from and reaps back into the same
/// scope, so `forall`s across a method's requires, ensures, and body consume
/// one flat pre-allocated id sequence.
pub(crate) struct QuantScope {
    ids: std::collections::VecDeque<vmir::MemberId>,
    out: Vec<(vmir::MemberId, vmir::Quantifier)>,
}

impl QuantScope {
    pub(crate) fn new(slots: &[(vmir::MemberId, DeclSlot<vmir::Quantifier>)]) -> Self {
        QuantScope {
            ids: slots.iter().map(|(id, _)| *id).collect(),
            out: Vec::new(),
        }
    }

    /// Hand the remaining occurrence ids to a fresh sink.
    pub(crate) fn seed(&mut self, sink: &mut crate::translate::sink::Sink) {
        sink.quant_ids = std::mem::take(&mut self.ids);
    }

    /// Take back the unconsumed ids and collect the quantifiers the sink built.
    pub(crate) fn reap(&mut self, sink: &mut crate::translate::sink::Sink) {
        self.ids = std::mem::take(&mut sink.quant_ids);
        self.out.append(&mut sink.quant_out);
    }

    /// All built quantifiers; panics if any pre-allocated id was never consumed
    /// (the declare-phase count and the lowering disagree).
    pub(crate) fn finish(self) -> Vec<(vmir::MemberId, vmir::Quantifier)> {
        assert!(
            self.ids.is_empty(),
            "forall occurrence slots over-allocated"
        );
        self.out
    }
}

/// The write side of translation: allocates and fills `Declaration` slots.
/// Holds no shared read state (`name_map`, `contracts`, ...) — that lives in the
/// coordinator's `TranslationContext`, a value entirely independent of
/// `Builder` (see `context.rs`'s module doc for why that separation matters).
/// Co-located with [`DeclSlot`] so it is the *only* code that can mint or fill a
/// slot.
pub(crate) struct Builder {
    /// Cheap string repr for member/constructor names. Keys are independent of
    /// `MemberId` — names are mapped to ids via `decl_names`.
    vmir_interner: Rodeo,
    /// Each declaration's name, parallel to `decls` (→ `Program.names`).
    decl_names: Vec<Spur>,
    /// Location **group** tags (`Type::Addr.group`) — field/predicate names,
    /// resolvable at verify time via `Program.groups`.
    groups: Rodeo<Spur>,
    /// Declarations indexed by `MemberId`. `None` slots are filled by
    /// `DeclSlot` consumption (`Definer::define_*`).
    decls: Vec<Option<vmir::Declaration>>,
}

impl Builder {
    pub(crate) fn new() -> Self {
        Self {
            vmir_interner: Rodeo::new(),
            decl_names: Vec::new(),
            groups: Rodeo::new(),
            decls: Vec::new(),
        }
    }

    /// A clone of the group interner, taken by the coordinator once `declare`
    /// finishes (fields/predicates register all groups during `declare`).
    pub(crate) fn clone_groups(&self) -> Rodeo<Spur> {
        self.groups.clone()
    }

    /// Reserve a `Declaration` slot (filled via `set_decl`), recording its name.
    /// `MemberId` is just the slot index; the interner key is unrelated.
    fn fresh_decl(&mut self, name: &str) -> vmir::MemberId {
        let id = vmir::MemberId(self.decls.len());
        let name_spur = self.vmir_interner.get_or_intern(name);
        self.decl_names.push(name_spur);
        self.decls.push(None);
        id
    }

    fn set_decl(&mut self, id: vmir::MemberId, decl: vmir::Declaration) {
        let slot = &mut self.decls[usize::from(id)];
        debug_assert!(slot.is_none(), "decl slot filled twice");
        *slot = Some(decl);
    }

    pub(crate) fn finalize(self) -> vmir::Program {
        // The single "every reserved slot was filled" check (replaces the old
        // per-slot drop-bomb). A `None` here means a translator declared a
        // member but never defined it — a bug; name it for a useful panic.
        let decls: TiVec<vmir::MemberId, vmir::Declaration> = self
            .decls
            .into_iter()
            .enumerate()
            .map(|(i, o)| {
                o.unwrap_or_else(|| {
                    let name = self.vmir_interner.resolve(&self.decl_names[i]);
                    panic!("declaration slot for `{name}` (MemberId {i}) left unfilled");
                })
            })
            .collect();
        vmir::Program {
            decls,
            interner: self.vmir_interner,
            groups: self.groups,
        }
    }
}

impl Declarator for Builder {
    fn alloc_slot<T>(&mut self, name: &str) -> (vmir::MemberId, DeclSlot<T>) {
        let id = self.fresh_decl(name);
        (id, DeclSlot::new(id))
    }

    fn intern_group(&mut self, s: &str) -> Spur {
        self.groups.get_or_intern(s)
    }
}

impl Definer for Builder {
    fn define_function(&mut self, slot: DeclSlot<vmir::Function>, decl: vmir::Function) {
        let id = slot.fill();
        self.set_decl(id, vmir::Declaration::Function(decl));
    }

    fn define_resource(&mut self, slot: DeclSlot<vmir::Resource>, decl: vmir::Resource) {
        let id = slot.fill();
        self.set_decl(id, vmir::Declaration::Resource(decl));
    }

    fn define_method(&mut self, slot: DeclSlot<vmir::Method>, decl: vmir::Method) {
        let id = slot.fill();
        self.set_decl(id, vmir::Declaration::Method(decl));
    }

    fn define_adt(&mut self, slot: DeclSlot<vmir::Adt>, decl: vmir::Adt) {
        let id = slot.fill();
        self.set_decl(id, vmir::Declaration::Adt(decl));
    }

    fn define_domain(&mut self, slot: DeclSlot<vmir::Domain>, decl: vmir::Domain) {
        let id = slot.fill();
        self.set_decl(id, vmir::Declaration::Domain(decl));
    }

    fn define_axiom(&mut self, slot: DeclSlot<vmir::Axiom>, decl: vmir::Axiom) {
        let id = slot.fill();
        self.set_decl(id, vmir::Declaration::Axiom(decl));
    }

    fn define_quantifier(&mut self, slot: DeclSlot<vmir::Quantifier>, decl: vmir::Quantifier) {
        let id = slot.fill();
        self.set_decl(id, vmir::Declaration::Quantifier(decl));
    }

    fn intern_name(&mut self, s: &str) -> Spur {
        self.vmir_interner.get_or_intern(s)
    }
}
