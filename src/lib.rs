#![feature(trait_alias)]
#![feature(never_type)]
#![feature(associated_type_defaults)]
pub mod pipeline;
pub mod silver;
pub mod translate;
mod util;
pub mod verify;
pub mod vmir;
pub use silver::silver_parser;
pub use util::*;
