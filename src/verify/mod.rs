//! Verification module for VMIR programs.
//!
//! This module implements symbolic execution and verification of VMIR programs,
//! focusing initially on separation logic (heap permissions).

pub mod term;
pub mod store;
pub mod chunk;
pub mod heap;
pub mod state;
pub mod operations;

pub use state::State;
