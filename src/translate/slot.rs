//! Declaration slots — an **unforgeable, affine write capability**, and
//! [`Builder`], the sole authority that mints and fills them.
//!
//! A [`DeclSlot<T>`] is a write-capability token for exactly one declaration
//! slot. It replaces the informal "don't forget to fill every slot" discipline
//! with a compile-time-enforced one: `#[must_use]`, non-`Clone`, and panics on
//! drop if never filled (a "drop bomb"). `Definer::define_*` consumes a
//! `DeclSlot<T>` by value, so "filled twice" is unrepresentable.
//!
//! **Unforgeable.** `DeclSlot::new` and `DeclSlot::fill` are private to *this*
//! module, and `Builder` (which owns the only `Declarator`/`Definer` impls)
//! lives here too. The translator submodules (`field`, `adt`, …) are
//! *siblings* of this module, not descendants, so they cannot reach the private
//! constructor or filler: a translator can hold a slot, hand it to `define_*`,
//! or `abandon` it — but can neither fabricate nor fill one. This is what makes
//! `Builder::alloc_slot` the single source of every slot.

use std::marker::PhantomData;

use lasso::{Rodeo, Spur};
use typed_index_collections::TiVec;

use crate::vmir;

/// A write-capability token for the declaration slot `id`. `T` is the `vmir`
/// declaration payload type the slot will hold (`vmir::Function`,
/// `vmir::Resource`, `vmir::Method`, `vmir::Adt`, `vmir::Domain`) — a phantom
/// marker only, never constructed.
#[must_use = "A DeclSlot represents an obligation to define a member. It must be filled."]
pub(crate) struct DeclSlot<T> {
    id: vmir::MemberId,
    filled: bool,
    _marker: PhantomData<T>,
}

impl<T> DeclSlot<T> {
    /// Mint a fresh, unfilled slot for `id`. **Private to `slot`** — only
    /// [`Builder::alloc_slot`] calls it, which is what makes a slot unforgeable
    /// outside this module.
    fn new(id: vmir::MemberId) -> Self {
        Self {
            id,
            filled: false,
            _marker: PhantomData,
        }
    }

    /// Consume the slot, marking it filled, and hand back its id so the
    /// `Definer` impl can write the actual `Declaration` there. **Private to
    /// `slot`** — only `Builder`'s `Definer` impl fills a slot.
    fn fill(mut self) -> vmir::MemberId {
        self.filled = true;
        self.id
    }

    /// Mark this slot filled **without** writing a decl. Used on an error path
    /// where a fallible `Translator::define` bails out before the point that
    /// would normally fill it — without this, the drop bomb would panic on top
    /// of the original `TranslationError`, turning a clean error return into a
    /// crash. Crate-visible: translators legitimately abandon their *own*
    /// slots, but still cannot forge or fill one.
    pub(crate) fn abandon(mut self) {
        self.filled = true;
    }
}

impl<T> Drop for DeclSlot<T> {
    fn drop(&mut self) {
        if !self.filled {
            panic!(
                "DeclSlot<{}> for {:?} dropped unfilled",
                std::any::type_name::<T>(),
                self.id
            );
        }
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

    fn intern_name(&mut self, s: &str) -> Spur;
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
        let decls: TiVec<vmir::MemberId, vmir::Declaration> = self
            .decls
            .into_iter()
            .map(|o| o.expect("declaration slot left empty"))
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

    fn intern_name(&mut self, s: &str) -> Spur {
        self.vmir_interner.get_or_intern(s)
    }
}
