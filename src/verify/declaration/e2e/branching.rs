//! Branching-focused tests: fold/exhale established on one arm vs both,
//! interacting with the join.

use super::*;

#[test]
fn fold_on_both_arms_available_past_join() {
    let input = r#"
field f: Int

predicate cell(r: Ref)
{ acc(r.f) }

method client(r: Ref, c: Bool)
{
    inhale acc(r.f)

    if (c) {
        fold cell(r)
    } else {
        fold cell(r)
    }

    unfold cell(r)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn fold_on_one_arm_only_unavailable_past_join() {
    // Fold-flavored sibling of `branch_establishing_resource_on_one_arm_only_fails`
    // (which uses raw `acc`) -- the fold itself must be branch-scoped too.
    let input = r#"
field f: Int

predicate cell(r: Ref)
{ acc(r.f) }

method client(r: Ref, c: Bool)
{
    inhale acc(r.f)

    if (c) {
        fold cell(r)
    }

    unfold cell(r)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(
        matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::InsufficientPermission)),
        "expected InsufficientPermission, got {result:?}"
    );
}
