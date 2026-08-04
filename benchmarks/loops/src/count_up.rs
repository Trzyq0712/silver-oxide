//! Loop corpus: the simplest possible loop, no annotations at all.
//!
//! Prusti infers the *permission* part of a loop invariant from the PCG
//! (`get_loop_inv`); the functional part would come from `body_invariant!`.
//! With neither, this shows the bare shape our lowering must consume.
//!
//!     PRUSTI_CHECK_OVERFLOWS=false PRUSTI_DUMP_VIPER_PROGRAM=true \
//!         prusti-rustc --crate-type=lib --edition=2021 count_up.rs

pub fn count_up(n: i32) -> i32 {
    let mut i = 0;
    while i < n {
        i += 1;
    }
    i
}
