//! `wildcard` permission tests: source-level wildcards in method in/exhale, the
//! field upper bound, and the function-context auto-wildcarding that lets a
//! read-only function unfold a predicate it also passes on (which full
//! permission cannot).

use super::*;

#[test]
fn inhale_wildcard_field_then_read() {
    // A `wildcard` inhale grants *some* positive share — enough to frame a read.
    let input = r#"
field f: Int

method client(x: Ref)
{
    inhale acc(x.f, wildcard)
    assert x.f == x.f
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(
        result.is_ok(),
        "a wildcard share frames a field read, got {result:?}"
    );
}

#[test]
fn exhale_wildcard_from_empty_fails() {
    // A wildcard is provably positive, so it cannot be taken from an empty
    // location (Silicon's `consumeGreedy` returns `Incomplete`).
    let input = r#"
field f: Int

method client(x: Ref)
{
    exhale acc(x.f, wildcard)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::InsufficientPermission)),
        "exhaling a wildcard from nothing must fail, got {result:?}"
    );
}

#[test]
fn exhale_wildcard_after_inhale_succeeds() {
    // Holding a positive share, a wildcard exhale assumes `w < held` and leaves a
    // positive remainder — it succeeds and never empties the chunk.
    let input = r#"
field f: Int

method client(x: Ref)
{
    inhale acc(x.f)
    exhale acc(x.f, wildcard)
    assert x.f == x.f
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(
        result.is_ok(),
        "a wildcard exhale from a held chunk keeps a positive remainder, got {result:?}"
    );
}

#[test]
fn two_wildcards_do_not_sum_to_full() {
    // Two wildcard shares stay bounded by the field cap (`≤ 1`) but need not sum
    // to a full `1/1`, so a subsequent full exhale must fail.
    let input = r#"
field f: Int

method client(x: Ref)
{
    inhale acc(x.f, wildcard)
    inhale acc(x.f, wildcard)
    exhale acc(x.f, 1/1)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::InsufficientPermission)),
        "two wildcards do not add up to full permission, got {result:?}"
    );
}

#[test]
fn function_precondition_source_wildcard_verifies() {
    // An explicit `wildcard` in a function precondition frames the body read.
    let input = r#"
field f: Int

function get(x: Ref): Int
    requires acc(x.f, wildcard)
{ x.f }
"#;
    let program = lower(input);
    let result = verify_named_function(&program, "get");
    assert!(
        result.is_ok(),
        "a wildcard-precondition function must verify, got {result:?}"
    );
}

#[test]
fn function_nested_unfold_succeeds_with_wildcard() {
    // THE wildcard win. `get2` unfolds `P(this)` and, *inside* that unfold, calls
    // `get(this)` which itself requires `P(this)`. Because function preconditions
    // (and the `unfolding` share) are lowered to wildcards, the unfold consumes
    // only `w < held`, leaving a positive remainder — so the nested `get(this)`
    // still finds a positive `P(this)` share. With full permission the outer
    // unfold would consume all of `P(this)` and the nested call would fail (see
    // `method_nested_unfold_with_full_perm_fails`).
    let input = r#"
field v: Int

predicate P(this: Ref)
{ acc(this.v) }

function get(this: Ref): Int
    requires acc(P(this))
{ unfolding P(this) in this.v }

function get2(this: Ref): Int
    requires acc(P(this))
{ unfolding P(this) in this.v + get(this) }
"#;
    let program = lower(input);
    assert!(
        verify_named_function(&program, "get").is_ok(),
        "get must verify"
    );
    let result = verify_named_function(&program, "get2");
    assert!(
        result.is_ok(),
        "a function unfolding a predicate it also passes on must verify under \
         wildcard permissions, got {result:?}"
    );
}

#[test]
fn method_nested_unfold_with_full_perm_fails() {
    // The contrast to `function_nested_unfold_succeeds_with_wildcard`: a **method**
    // `unfolding` uses the *full* written permission (methods are not read-only),
    // so `unfolding P(this)` consumes all of `P(this)` and the nested `get(this)`
    // — which requires `P(this)` — finds nothing left.
    let input = r#"
field v: Int

predicate P(this: Ref)
{ acc(this.v) }

function get(this: Ref): Int
    requires acc(P(this))
{ unfolding P(this) in this.v }

method client(this: Ref)
    requires acc(P(this))
{
    var t: Int := unfolding P(this) in this.v + get(this)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(
        result.is_err(),
        "a full-permission unfold leaves nothing for the nested call, got {result:?}"
    );
}
