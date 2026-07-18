//! Predicate-focused tests: fold/unfold body conjuncts, argument-identity,
//! and pure (heap-free) predicate bodies.

use super::*;

#[test]
fn fold_checks_body_conjunct_not_just_field_presence() {
    // `zeroed`'s body pairs a heap chunk with a pure constraint on its
    // value. Folding when the constraint doesn't hold must fail, not just
    // check the field is present.
    let input = r#"
field f: Int

predicate zeroed(r: Ref)
{ acc(r.f) && r.f == 0 }

method client(r: Ref)
{
    inhale acc(r.f)
    r.f := 1

    fold zeroed(r)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(
        result.is_err(),
        "fold should fail when the body conjunct r.f == 0 doesn't hold, got {result:?}"
    );
}

#[test]
fn unfold_without_held_permission_fails() {
    // Unfolding a predicate instance the method never inhaled must fail.
    let input = r#"
field f: Int

predicate cell(r: Ref)
{ acc(r.f) }

method client(r: Ref)
{
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

#[test]
fn predicate_argument_identity_keeps_instances_independent() {
    // Folding/unfolding `cell(x)` must not touch the permission held for
    // `cell(y)` when `x != y` -- instances are identified by argument.
    let input = r#"
field f: Int

predicate cell(r: Ref)
{ acc(r.f) }

method client(x: Ref, y: Ref)
{
    inhale acc(x.f) && acc(y.f) && x != y

    fold cell(x)

    assert perm(y.f) == write
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn pure_bool_predicate_body_carries_fact_through_unfold() {
    // A predicate body with NO heap access, just a pure boolean: inhaling
    // `q(false)` assumes `false` in the path even though there's no chunk
    // to produce, so unfolding must deliver that fact. Same shape of bug
    // class as `../../../cases/pred_merge.vpr` (a pure conjunct hiding
    // inside a predicate body that a syntactic-only framer could drop).
    let input = r#"
predicate q(b: Bool)
{ b }

method client()
{
    inhale acc(q(false))
    unfold q(false)

    assert false
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}
