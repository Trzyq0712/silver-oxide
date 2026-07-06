//! Per-declaration translators — exactly one per Viper `typed::Declaration`
//! (field, predicate, function, method, adt, domain). Each runs the
//! `declare → meta → define` typestate phases described in the parent module,
//! self-publishing its metadata into `TranslationContext` and consuming its
//! `DeclSlot`s (from the sibling `slot` module) to emit `vmir::Declaration`s.

mod adt;
mod domain;
mod field;
mod function;
mod method;
mod predicate;

pub(crate) use adt::AdtTranslator;
pub(crate) use domain::DomainTranslator;
pub(crate) use field::FieldTranslator;
pub(crate) use function::FunctionTranslator;
pub(crate) use method::MethodTranslator;
pub(crate) use predicate::PredicateTranslator;
