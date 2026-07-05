//! `Hole<T>` — an affine write-capability token for exactly one declared
//! member. Replaces the informal "don't forget to fill every slot" discipline
//! (a `debug_assert!` mid-pipeline plus a final `.expect()` sweep) with a
//! compile-time-enforced one: a `Hole` is `must_use`, non-`Clone`, and panics
//! on drop if it was never filled (a "drop bomb"). `Definer::define_*`
//! consumes a `Hole<T>` by value, so "filled twice" becomes unrepresentable —
//! the `Hole` is moved and gone after one call.

use lasso::Spur;

use crate::vmir;

/// A write-capability token for the declaration slot `id`. `T` is the `vmir`
/// declaration payload type the slot will eventually hold (`vmir::Function`,
/// `vmir::Resource`, `vmir::Method`, `vmir::Adt`, `vmir::Domain`) — a
/// phantom marker only, never constructed.
#[must_use = "A Hole represents an obligation to define a member. It must be filled."]
pub(crate) struct Hole<T> {
    id: vmir::MemberId,
    filled: bool,
    _marker: std::marker::PhantomData<T>,
}

impl<T> Hole<T> {
    /// Mint a fresh, unfilled hole for `id`. Only [`Declarator::allocate_hole`]
    /// impls call this — it carries the same obligation `fresh_decl` used to
    /// (a reserved `None` slot elsewhere in `decls`).
    pub(crate) fn new(id: vmir::MemberId) -> Self {
        Self {
            id,
            filled: false,
            _marker: std::marker::PhantomData,
        }
    }

    /// Consume the hole, marking it filled, and hand back its id so the
    /// `Definer` impl can write the actual `Declaration` at that slot.
    pub(crate) fn fill(mut self) -> vmir::MemberId {
        self.filled = true;
        self.id
    }

    /// Mark this hole filled **without** writing a decl. Used on an error
    /// path where a fallible `Translator::define` bails out (`?`) before
    /// reaching the point that would normally fill it — without this, the
    /// drop bomb would panic on top of the original `TranslationError`,
    /// turning a clean error return into a crash.
    pub(crate) fn abandon(mut self) {
        self.filled = true;
    }
}

impl<T> Drop for Hole<T> {
    fn drop(&mut self) {
        if !self.filled {
            panic!(
                "Hole<{}> for {:?} dropped unfilled",
                std::any::type_name::<T>(),
                self.id
            );
        }
    }
}

/// Allocates declaration slots. `allocate_hole::<T>` reserves a slot (interns
/// the display name, pushes a `None` decl) and returns its id paired with the
/// `Hole<T>` write capability for that slot.
pub(crate) trait Declarator {
    fn allocate_hole<T>(&mut self, name: &str) -> (vmir::MemberId, Hole<T>);

    /// Register a field/predicate name as a location **group** tag
    /// (`Type::Addr.group`), interned separately from `Declaration` names.
    fn intern_group(&mut self, s: &str) -> Spur;
}

/// Fills declaration slots, one method per `vmir` payload kind, each
/// consuming the matching `Hole<T>` by value. Also exposes the mid-`define`
/// string interning `declare`-time helpers don't need.
pub(crate) trait Definer {
    fn define_function(&mut self, hole: Hole<vmir::Function>, decl: vmir::Function);
    fn define_resource(&mut self, hole: Hole<vmir::Resource>, decl: vmir::Resource);
    fn define_method(&mut self, hole: Hole<vmir::Method>, decl: vmir::Method);
    fn define_adt(&mut self, hole: Hole<vmir::Adt>, decl: vmir::Adt);
    fn define_domain(&mut self, hole: Hole<vmir::Domain>, decl: vmir::Domain);

    fn intern_name(&mut self, s: &str) -> Spur;
}
