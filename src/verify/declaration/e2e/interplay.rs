//! Tests that specifically combine two or more of permissions / predicates /
//! branching / functions in one shape, as opposed to the single-topic tests
//! in the sibling modules.

use super::*;

#[test]
fn branch_selects_predicate_instance_by_argument() {
    // Which predicate instance gets folded depends on the branch; using
    // whichever one the taken branch actually established must work, and
    // must not accidentally borrow permission from the other instance.
    let input = r#"
field f: Int

predicate cell(r: Ref)
{ acc(r.f) }

method client(x: Ref, y: Ref, c: Bool)
{
    inhale acc(x.f) && acc(y.f)

    if (c) {
        fold cell(x)
    } else {
        fold cell(y)
    }

    if (c) {
        unfold cell(x)
        assert perm(x.f) == write
    } else {
        unfold cell(y)
        assert perm(y.f) == write
    }
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn heap_dep_function_call_guarded_by_branch_needs_fold_on_both_arms() {
    // A heap-dependent function's `Snap` needs the predicate footprint;
    // folding it on only one arm before a call that runs on both arms
    // must fail on the arm that didn't fold.
    let input = r#"
field f: Int

predicate cell(r: Ref)
{ acc(r.f) }

function get(r: Ref): Int
    requires acc(cell(r), write)
{
    unfolding acc(cell(r), write) in r.f
}

method client(r: Ref, c: Bool)
{
    inhale acc(r.f)

    if (c) {
        fold cell(r)
    }

    var a: Int := get(r)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(
        matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::InsufficientPermission)),
        "expected InsufficientPermission, got {result:?}"
    );
}
