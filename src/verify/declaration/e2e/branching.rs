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

// ---- `f%pre` token release under the call's path condition -----------------
//
// A call site mints the callee's `f%pre(args)` token: its *presence* lets the
// unfold rule materialize the callee's body here, its *truth* releases the
// resulting axioms (`tok ==> f == body`, `tok ==> each exported fact`). The truth
// is assumed under the call's path condition, so a call under a ternary or an
// implication must not release the callee's facts onto a sibling intra-block
// path. CFG-level branches are separately isolated by the fork/block model; these
// tests cover the intra-block `PcKind`s, which are the ones the token carries.

#[test]
fn ternary_call_does_not_leak_callee_ensures() {
    // `g` has no precondition, so the callee-side guard chain (its `#requires`
    // application, then its own internal pc) is vacuous — the caller's token is
    // the only thing that can confine `ensures false` to the `b` arm. A failing
    // assertion means *every* tier rejected, so this covers the ground graph, the
    // block scratch and the probe clone in one test.
    let input = r#"
function g(a: Int): Bool
  ensures false

method client(v: Int, b: Bool)
{
    var r: Bool := b ? g(v) : true
    assert false
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "client").is_err(),
        "`ensures false` from a call under `b` must not reach the `!b` path"
    );
}

#[test]
fn implication_guarded_call_does_not_leak_callee_ensures() {
    // The `PcKind::Fact` analogue of the test above: an implication, not a
    // ternary. Both intra-block kinds must confine the release.
    let input = r#"
function g(a: Int): Bool
  ensures false

method client(v: Int, b: Bool)
{
    var r: Bool := b ==> g(v)
    assert false
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "client").is_err(),
        "`ensures false` from a call under `b ==> _` must not reach the `!b` path"
    );
}

#[test]
fn ternary_call_ensures_available_on_its_own_branch() {
    // Non-vacuity for the tests above: the guard must *collapse* where the call
    // does occur, which happens in the probe clone that assumes the goal's pc.
    // Without that, gating would trade a leak for lost completeness.
    let input = r#"
function g(a: Int): Int
  ensures result == 7

method client(v: Int, b: Bool)
{
    var r: Int := b ? g(v) : 7
    assert r == 7
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "client").is_ok(),
        "the callee's post must still be available on the branch that calls it"
    );
}

#[test]
fn unconditional_call_still_unfolds() {
    // The definitional axiom is no longer an e-class merge when a token is
    // present: it is `ite(tok, f(args) == body, true) == true`, which needs
    // `ite-reduce` then `eq-true-union` to land the merge. This is the
    // dominant shape in the corpus, so it is worth pinning on its own.
    let input = r#"
function inc(x: Int): Int
{ x + 1 }

method client(v: Int)
{
    var a: Int := inc(v)
    assert a == v + 1
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "client").is_ok(),
        "an unconditional call must still unfold its body"
    );
}

#[test]
fn branch_conditional_call_still_unfolds_under_its_branch() {
    // The guarded definitional equality with the guard collapsing only inside the
    // probe clone — the conditional counterpart of the test above.
    let input = r#"
function inc(x: Int): Int
{ x + 1 }

method client(v: Int, b: Bool)
{
    var a: Int := b ? inc(v) : 0
    assert b ==> a == v + 1
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "client").is_ok(),
        "a conditional call must unfold under its own branch"
    );
}

#[test]
fn nested_call_definition_reaches_client() {
    // `six`'s body propagates `five%pre` as an ordinary step whose value is never
    // read (`bodyPreconditionPropagation`). Adding that node only makes `five`
    // *materializable*; releasing its truth under `six%pre` is what activates
    // `five`'s own definition, so this is the guard for that plumbing.
    let input = r#"
function five(): Int { 5 }
function six(): Int { five() + 1 }

method client()
{
    assert six() == 6
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "client").is_ok(),
        "a nested callee's definition must reach a transitive client"
    );
}

#[test]
fn call_with_no_occurrence_never_instantiates() {
    // The other end of the range: with no call at all the token is absent, so the
    // rule never materializes the body and the post never arrives. Correct before
    // this gating too — kept so a future change cannot re-widen the token
    // silently.
    let input = r#"
function g(a: Int): Bool
  ensures false

method client(v: Int)
{
    assert false
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "client").is_err(),
        "an uncalled function's post must not be instantiated"
    );
}
