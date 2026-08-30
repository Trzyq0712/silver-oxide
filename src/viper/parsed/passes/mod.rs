//! Pre-typecheck rewrite passes over the parsed AST.

mod disambiguate;
mod macro_expand;

pub use disambiguate::{disambiguate, disambiguate_reporting};
pub use macro_expand::inline_macros;
