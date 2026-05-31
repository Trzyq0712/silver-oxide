//! Stage 1: the initial parsed Viper AST, mutated in place by the
//! interner/disambiguator/macro passes before typechecking.

pub mod ast;
pub mod passes;

mod ast_ext;
mod builtins;

pub use ast::*;
pub use passes::{disambiguate, inline_macros};
