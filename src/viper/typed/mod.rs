//! Stage 2: the typechecked Viper AST, produced by `typecheck` and consumed
//! by translation.

pub mod ast;
pub mod display;

pub use ast::*;
pub use display::{Show, show};
