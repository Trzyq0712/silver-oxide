//! Function-focused tests: permission threading through heap-dependent call
//! chains, distinct from the pure heap-free contract-propagation tests in
//! `mod.rs` (`function_post_propagates_transitively` and friends).

use super::*;

#[test]
fn heap_dep_call_chain_threads_footprint_through_two_hops() {
    // `outer` calls `inner`, which itself calls `get` -- the footprint
    // sufficiency check at each `Snap` must thread through both hops using
    // only the single `acc(x.f)` the top-level caller holds.
    let input = r#"
field f: Int

function get(x: Ref): Int
    requires acc(x.f)
{ x.f }

function inner(x: Ref): Int
    requires acc(x.f)
{ get(x) + 1 }

function outer(x: Ref): Int
    requires acc(x.f)
{ inner(x) + 1 }

method m(y: Ref)
    requires acc(y.f)
{
    var a: Int := outer(y)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn heap_dep_call_chain_missing_footprint_at_outer_hop_fails() {
    // Same chain, but `m` holds no permission at all -- the very first
    // `Snap` (at `outer`'s call site) must fail, not silently succeed
    // because a deeper hop happens to need less.
    let input = r#"
field f: Int

function get(x: Ref): Int
    requires acc(x.f)
{ x.f }

function inner(x: Ref): Int
    requires acc(x.f)
{ get(x) + 1 }

function outer(x: Ref): Int
    requires acc(x.f)
{ inner(x) + 1 }

method m(y: Ref)
{
    var a: Int := outer(y)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::InsufficientPermission)),
        "expected InsufficientPermission, got {result:?}"
    );
}
