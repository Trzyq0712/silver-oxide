//! End-to-end verification tests: lower a Silver source string through the
//! full pipeline (parse → … → translate) and verify, asserting pass/fail and
//! specific `VerifyError` variants. The e-graph unit tests stay in `super`'s
//! `mod tests`.

use super::*;
use crate::translate;
use crate::viper::{
    GlobalsCollector, IdentCollector, disambiguate, inline_macros, typecheck_program, viper_parser,
    walk::AstWalkable,
};

fn lower(input: &str) -> vmir::Program {
    let mut program = viper_parser::vpr_program(input).expect("parse");
    let mut ic = IdentCollector::default();
    program.walk_mut(&mut ic);
    let interner = ic.finalize();
    let mut gc = GlobalsCollector::new(&interner);
    program.walk(&mut gc);
    let globals = gc.finalize().expect("globals");
    disambiguate(&mut program, &interner, &globals).expect("disambiguation");
    inline_macros(&mut program, &interner).expect("macros");
    let typed = typecheck_program(&mut program, &interner, &globals).expect("typecheck");
    // `Option` is a verifier builtin (the mono allocator registers it), not a
    // program declaration — nothing to inject here.
    translate::translate(&typed, &interner, &globals).expect("translate")
}

#[test]
fn double_consume_predicate_should_fail() {
    let input = r#"
predicate number(this: Ref)

method consume(this: Ref)
    requires number(this)

method caller(this: Ref)
    requires number(this)
{
    consume(this)
    consume(this)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "caller");
    assert!(
        matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::InsufficientPermission)),
        "expected InsufficientPermission, got {result:?}"
    );
}

#[test]
fn ensures_does_not_double_count_carried_permission() {
    // `read` requires AND ensures `number(this)`. The ensures delta must be
    // produced-only (perm 1), not accumulated onto the requires delta
    // (which would yield perm 2). Likewise `add` carries number(this)/
    // number(other) through and adds number(res); every chunk stays at 1.
    let input = r#"
predicate number(this: Ref)

method assign(this: Ref, value: Int)
    ensures number(this)

method read(this: Ref) returns (val: Int)
    requires number(this)
    ensures number(this)

method add(this: Ref, other: Ref) returns (res: Ref)
    requires number(this) && number(other)
    ensures number(this) && number(other) && number(res)
{
    var a: Int := read(this)
    var b: Int := read(other)
    var sum: Int := a + b
    assign(res, sum)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "add");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn exhale_exceeding_held_permission_fails() {
    // `client` holds only `1/2` of `acc(x.f)` but calls `needs_full`, whose
    // precondition exhales the full `1/1`. The exhale would drive the
    // permission to `-1/2`, so verification must fail rather than allow a
    // negative permission.
    let input = r#"
field f: Int

method needs_full(x: Ref)
    requires acc(x.f, 1/1)

method client(x: Ref)
    requires acc(x.f, 1/2)
{
    needs_full(x)
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
fn branch_preserves_held_permission_through_both_arms() {
    // `m` holds `acc(x.f)` and neither arm of the `if` touches it, so the
    // permission must still be held at the merge to discharge the `ensures`.
    // Exercises CFG linearization: per-block path conditions and the single
    // linear heap threaded across both arms.
    let input = r#"
field f: Int

method m(c: Bool, x: Ref)
    requires acc(x.f, 1/1)
    ensures acc(x.f, 1/1)
{
    if (c) { } else { }
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn branch_establishing_resource_on_one_arm_only_fails() {
    // `give` establishes `number(this)`, but it is only called on the `c` arm.
    // On the `!c` arm the predicate is never produced, so the `ensures` cannot
    // hold unconditionally — the per-arm permission gating must surface this as
    // insufficient permission rather than (unsoundly) verifying.
    let input = r#"
predicate number(this: Ref)

method give(this: Ref)
    ensures number(this)

method m(c: Bool, this: Ref)
    ensures number(this)
{
    if (c) { give(this) } else { }
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::InsufficientPermission)),
        "expected InsufficientPermission, got {result:?}"
    );
}

#[test]
fn goto_three_way_join_is_not_a_diamond() {
    // A merge reached three ways (`goto M` from each `if`, plus fall-through) is
    // only constructible with `goto` — it is not a clean `c ∨ !c` diamond, so it
    // exercises the materialized-OR reach fallback (`pc = <a ∨ (!a∧b) ∨ (!a∧!b)>`).
    // No arm touches `x.f`, so the permission survives and `ensures` holds; the
    // verifier assumes the (tautological) reach literal to discharge it.
    let input = r#"
field f: Int

method m(a: Bool, b: Bool, x: Ref)
    requires acc(x.f, 1/1)
    ensures acc(x.f, 1/1)
{
    if (a) { goto done }
    if (b) { goto done }
    label done
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn forward_goto_skips_dead_block() {
    // The `exhale` between `goto skip` and `label skip` is unreachable, so the
    // linearizer drops it (reachability filter) and the permission is retained.
    let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 1/1)
    ensures acc(x.f, 1/1)
{
    goto skip
    exhale acc(x.f, 1/1)
    label skip
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn crossing_non_planar_control_flow() {
    // `X` and `Y` both branch on `b` but to *swapped* targets `P`/`Q` — a
    // crossing (non-planar) CFG, only constructible with `goto`. The four edge
    // conditions `a∧b`, `a∧!b`, `!a∧b`, `!a∧!b` are pairwise exclusive, so each
    // join's two in-edges stay mutually exclusive (phi exhaustive) and the final
    // merge's reach is the tautology of all four. Planarity is irrelevant: the
    // linearizer only uses topological order and per-edge reach conditions.
    let input = r#"
field f: Int

method m(a: Bool, b: Bool, x: Ref)
    requires acc(x.f, 1/1)
    ensures acc(x.f, 1/1)
{
    if (a) { goto x_blk } else { goto y_blk }
    label x_blk
    if (b) { goto p_blk } else { goto q_blk }
    label y_blk
    if (b) { goto q_blk } else { goto p_blk }
    label p_blk
    goto end_blk
    label q_blk
    goto end_blk
    label end_blk
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn value_postcondition_reflexive_and_copied() {
    // `ensures r == a` after `r := a` reduces to `a == a` — discharged by the
    // `eq-refl` rule (also covers a copy chain `t := a; r := t` via congruence).
    for body in ["r := a", "var t: Int := a  r := t"] {
        let input = format!("method m(a: Int) returns (r: Int) ensures r == a {{ {body} }}");
        let program = lower(&input);
        let result = verify_named_method(&program, "m");
        assert!(result.is_ok(), "body `{body}`: expected Ok, got {result:?}");
    }
}

/// Verify the resource interned under `name`, panicking if it is missing or
/// is not a `Resource`.
fn verify_named_resource(program: &vmir::Program, name: &str) -> Result<(), VerifyError> {
    let id = program
        .interner
        .get(name)
        .unwrap_or_else(|| panic!("missing resource {name}"));
    let vmir::Declaration::Resource(r) = &program.decls[id] else {
        panic!("{name} must be a Resource");
    };
    let mut alloc = crate::verify::mono::Allocator::new(program);
    // Build certificates for the *other* resources (dependency order ≈ decl
    // order for these small fixtures), tolerating failures, so a body that
    // unfolds another predicate can graft its certificate. The target itself is
    // skipped so a deliberately-failing target still returns `Err`.
    let mut certs = HashMap::new();
    for (cid, decl) in program.decls.iter_enumerated() {
        if cid == id {
            continue;
        }
        if let vmir::Declaration::Resource(cr) = decl {
            let cname = program.interner.resolve(&cid).to_string();
            if let Ok(Some(cert)) = verify_resource(program, &cname, cr, &certs, &mut alloc) {
                certs.insert(cid, cert);
            }
        }
    }
    verify_resource(program, name, r, &certs, &mut alloc).map(|_| ())
}

/// Build certificates for every resource in `program` (test helper). Shares the
/// `alloc` so certificate ids match the method's later use.
fn build_certs(
    program: &vmir::Program,
    alloc: &mut crate::verify::mono::Allocator,
) -> HashMap<MemberId, ResourceCertificate> {
    let mut certs = HashMap::new();
    for (id, decl) in program.decls.iter_enumerated() {
        if let vmir::Declaration::Resource(r) = decl {
            let name = program.interner.resolve(&id).to_string();
            if let Some(cert) =
                verify_resource(program, &name, r, &certs, alloc).expect("resource verifies")
            {
                certs.insert(id, cert);
            }
        }
    }
    certs
}

#[test]
fn resource_negative_permission_rejected() {
    // `acc(x.f, 1/1 - 2/1)` folds to permission -1 → side condition fails.
    let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 1/1 - 2/1)
"#;
    let program = lower(input);
    let result = verify_named_resource(&program, "m#requires");
    assert!(
        matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::SideCondition(_))),
        "expected SideCondition, got {result:?}"
    );
}

#[test]
fn resource_positive_permission_ok() {
    let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 1/1)
"#;
    let program = lower(input);
    let result = verify_named_resource(&program, "m#requires");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn resource_div_by_zero_rejected() {
    // `x / 0` in the precondition → divisor side condition fails.
    let input = r#"
method m(x: Int)
    requires x / 0 == x
"#;
    let program = lower(input);
    let result = verify_named_resource(&program, "m#requires");
    assert!(
        matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::SideCondition(_))),
        "expected SideCondition, got {result:?}"
    );
}

/// Verify the method `name`, panicking if missing or not a `Method`.
fn verify_named_method(program: &vmir::Program, name: &str) -> Result<(), VerifyError> {
    let id = program
        .interner
        .get(name)
        .unwrap_or_else(|| panic!("missing method {name}"));
    let vmir::Declaration::Method(m) = &program.decls[id] else {
        panic!("{name} must be a Method");
    };
    let mut alloc = crate::verify::mono::Allocator::new(program);
    let certs = build_certs(program, &mut alloc);
    verify_method(program, name, m, &certs, &mut alloc)
}

#[test]
fn adt_discriminator_on_known_constructor() {
    // `one()` is a known constructor, so `tag(one()) ⇒ 0`; the `istwo`
    // discriminator desugars to `tag(x) == 1`, which folds to `false`.
    let input = r#"
adt MyAdt { one() two() }
method m()
{
    var x: MyAdt := one()
    assert !x.istwo
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "!one().istwo should verify"
    );
}

#[test]
fn adt_discriminator_wrong_variant_fails() {
    // `one().istwo` is `false`, so asserting it must fail.
    let input = r#"
adt MyAdt { one() two() }
method m()
{
    var x: MyAdt := one()
    assert x.istwo
}
"#;
    let program = lower(input);
    assert!(
        matches!(
            verify_named_method(&program, "m"),
            Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)
        ),
        "asserting one().istwo should fail"
    );
}

#[test]
fn adt_destructor_projects_constructor_field() {
    // `mk(3,4).fst` projects to `3` via the projection reduction.
    let input = r#"
adt Pair { mk(fst: Int, snd: Int) }
method m()
{
    var p: Pair := mk(3, 4)
    assert p.fst == 3
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "mk(3,4).fst == 3 should verify"
    );
}

#[test]
fn adt_destructor_wrong_field_value_fails() {
    let input = r#"
adt Pair { mk(fst: Int, snd: Int) }
method m()
{
    var p: Pair := mk(3, 4)
    assert p.fst == 4
}
"#;
    let program = lower(input);
    assert!(
        matches!(
            verify_named_method(&program, "m"),
            Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)
        ),
        "mk(3,4).fst == 4 should fail"
    );
}

#[test]
fn generic_adt_two_monomorphizations() {
    // A user-written generic ADT used at two element types. Each
    // monomorphization (`Box[Int]`, `Box[Bool]`) gets its own verifier ids, so
    // both projections reduce correctly and don't congruence-merge.
    let input = r#"
adt Box[T] { mk(v: T) }
method m()
{
    var bi: Box[Int] := mk(5)
    var bb: Box[Bool] := mk(true)
    assert bi.v == 5
    assert bb.v == true
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "generic Box at Int and Bool should verify"
    );
}

#[test]
fn generic_adt_wrong_field_value_fails() {
    let input = r#"
adt Box[T] { mk(v: T) }
method m()
{
    var bi: Box[Int] := mk(5)
    assert bi.v == 6
}
"#;
    let program = lower(input);
    assert!(
        matches!(
            verify_named_method(&program, "m"),
            Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)
        ),
        "mk(5).v == 6 should fail"
    );
}

#[test]
fn fold_unfold_roundtrip_preserves_field() {
    // `fold` then `unfold` recovers the exact field value via the snapshot.
    let input = r#"
field f: Int
predicate Cell(x: Ref) { acc(x.f, write) }
method m(x: Ref)
  requires acc(x.f, write) && x.f == 5
{
  fold acc(Cell(x), write)
  unfold acc(Cell(x), write)
  assert x.f == 5
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "fold/unfold round-trip should preserve x.f == 5"
    );
}

#[test]
fn unfolding_expression_reads_field() {
    // `unfolding acc(Cell(x), write) in x.f` reads the field through a scoped
    // unfold without a preceding statement `unfold` — the predicate stays
    // folded afterwards (the unfolded heap is discarded).
    let input = r#"
field f: Int
predicate Cell(x: Ref) { acc(x.f, write) }
method m(x: Ref) returns (v: Int)
  requires acc(x.f, write) && x.f == 5
{
  fold acc(Cell(x), write)
  v := unfolding acc(Cell(x), write) in x.f
  assert v == 5
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "unfolding expression should read x.f == 5 through a scoped unfold"
    );
}

#[test]
fn unfolding_in_predicate_body_unfolds_nested() {
    // A predicate body holds a nested predicate and reads through it via
    // `unfolding`, verified by the shared resource-body unfold path (the cert
    // of the nested `Inner` is grafted).
    let input = r#"
field f: Int
predicate Inner(x: Ref) { acc(x.f, write) }
predicate Outer(x: Ref) {
  acc(Inner(x), write) && (unfolding acc(Inner(x), write) in x.f) == 0
}
"#;
    let program = lower(input);
    assert!(
        verify_named_resource(&program, "Outer").is_ok(),
        "Outer well-formedness should verify via nested unfold"
    );
}

#[test]
fn unfolding_in_predicate_body_without_holding_fails() {
    // `unfolding Inner(x)` without holding `acc(Inner(x))` lacks permission.
    let input = r#"
field f: Int
predicate Inner(x: Ref) { acc(x.f, write) }
predicate Bad(x: Ref) { (unfolding acc(Inner(x), write) in x.f) == 0 }
"#;
    let program = lower(input);
    assert!(
        matches!(
            verify_named_resource(&program, "Bad"),
            Err(ref e) if matches!(e.root_cause(), VerifyError::InsufficientPermission)
        ),
        "unfolding a predicate that is not held should lack permission"
    );
}

#[test]
fn unfolding_recursive_predicate_in_resource_body() {
    // A predicate body unfolds a *recursive* predicate one level by grafting
    // the unfolded predicate's certificate (`List` is verified first).
    let input = r#"
field val: Int
field next: Ref
predicate List(this: Ref) {
  acc(this.val, write) && acc(this.next, write) &&
  (this.next != null ==> List(this.next))
}
predicate Head(this: Ref) {
  acc(List(this), write) && (unfolding acc(List(this), write) in this.val) == 0
}
"#;
    let program = lower(input);
    assert!(
        verify_named_resource(&program, "Head").is_ok(),
        "Head should verify by inlining List one level (cert-free)"
    );
}

#[test]
fn fold_consumes_field_permission() {
    // After `fold`, the field permission has moved into the predicate, so a
    // direct read of `x.f` no longer has permission.
    let input = r#"
field f: Int
predicate Cell(x: Ref) { acc(x.f, write) }
method m(x: Ref)
  requires acc(x.f, write) && x.f == 5
{
  fold acc(Cell(x), write)
  assert x.f == 5
}
"#;
    let program = lower(input);
    assert!(
        matches!(
            verify_named_method(&program, "m"),
            Err(ref e) if matches!(e.root_cause(), VerifyError::InsufficientPermission)
        ),
        "reading x.f after fold should lack permission"
    );
}

#[test]
fn fold_unfold_two_field_predicate() {
    // A two-field predicate round-trips both fields (values set by
    // assignment to avoid the conjunction-assume gap on `&&` of facts).
    let input = r#"
field f: Int
field g: Int
predicate Pair(x: Ref) { acc(x.f, write) && acc(x.g, write) }
method m(x: Ref)
  requires acc(x.f, write) && acc(x.g, write)
{
  x.f := 1
  x.g := 2
  fold acc(Pair(x), write)
  unfold acc(Pair(x), write)
  assert x.f == 1
  assert x.g == 2
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "two-field fold/unfold round-trip should preserve both fields"
    );
}

#[test]
fn fold_unfold_conditional_true_branch() {
    // A predicate with a conditional acc (`b ==> acc(x.f)`): when the guard
    // is true the field is captured (member `Some(v)`), so the round-trip
    // recovers it. Exercises conditional folding + the optional discriminant
    // `0 < (b ? p : 0)` collapsing to `b`.
    let input = r#"
field f: Int
predicate Maybe(x: Ref, b: Bool) { b ==> acc(x.f, write) }
method m(x: Ref)
  requires acc(x.f, write) && x.f == 5
{
  fold acc(Maybe(x, true), write)
  unfold acc(Maybe(x, true), write)
  assert x.f == 5
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "conditional fold/unfold (guard true) should preserve x.f == 5"
    );
}

#[test]
fn fold_unfold_conditional_false_keeps_field() {
    // With the guard false the predicate captures nothing (member `None`),
    // so the field permission is retained and `x.f` is still readable.
    let input = r#"
field f: Int
predicate Maybe(x: Ref, b: Bool) { b ==> acc(x.f, write) }
method m(x: Ref)
  requires acc(x.f, write) && x.f == 5
{
  fold acc(Maybe(x, false), write)
  assert x.f == 5
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "conditional fold (guard false) should retain the field permission"
    );
}

#[test]
fn fold_unfold_mixed_element_types() {
    // A predicate over an Int and a Bool field: each field's snapshot member
    // monomorphises a distinct `Option` instance (`Some@Int` vs `Some@Bool`,
    // distinct member ids), and both round-trip independently.
    let input = r#"
field f: Int
field g: Bool
predicate Both(x: Ref) { acc(x.f, write) && acc(x.g, write) }
method m(x: Ref)
  requires acc(x.f, write) && acc(x.g, write)
{
  x.f := 7
  x.g := true
  fold acc(Both(x), write)
  unfold acc(Both(x), write)
  assert x.f == 7
  assert x.g == true
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "mixed Int/Bool fold/unfold round-trip should preserve both fields"
    );
}

#[test]
fn fold_unfold_aliased_footprint() {
    // Two `acc` on the *same* location: the footprint has two (unmerged)
    // slots, so the snapshot keeps two members, even though the merged
    // accounting view holds a single `x.f` chunk (perm 1/2 + 1/2 = write).
    let input = r#"
field f: Int
predicate dup(x: Ref) { acc(x.f, 1/2) && acc(x.f, 1/2) }
method m(x: Ref)
  requires acc(x.f, write) && x.f == 5
{
  fold dup(x)
  unfold dup(x)
  assert x.f == 5
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "aliased-footprint fold/unfold should preserve x.f == 5"
    );
}

#[test]
fn fold_unfold_fractional_with_pure_fact() {
    // Bare `fold`/`unfold P(x)` syntax, a predicate carrying a pure fact,
    // unfolding an opaque (requires-held) predicate, and a fractional
    // exhale/unfold round-trip preserving the snapshot value. (cases/folds.vpr)
    let input = r#"
field f: Int
predicate pos(x: Ref) { acc(x.f) && x.f > 0 }
method m(x: Ref)
    requires pos(x)
{
    unfold pos(x)
    assert x.f > 0
    x.f := 10
    fold pos(x)
    exhale acc(pos(x), 1/2)
    unfold acc(pos(x), 1/2)
    assert x.f > 0
    assert x.f == 10
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "folds.vpr scenario should verify"
    );
}

#[test]
fn inline_inhale_then_exhale_roundtrips() {
    // Inhale a field + a fact about it (read against the growing heap), then
    // exhale the fact (read against the pre-exhale heap) and the permission.
    let input = r#"
field f: Int

method m(x: Ref)
{
    inhale acc(x.f, 1/1) && x.f == 5
    exhale x.f == 5
    exhale acc(x.f, 1/1)
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "inhale/exhale roundtrip should verify"
    );
}

#[test]
fn inline_exhale_without_permission_fails() {
    // Exhaling `1/1` while only `1/2` was inhaled drives permission negative.
    let input = r#"
field f: Int

method m(x: Ref)
{
    inhale acc(x.f, 1/2)
    exhale acc(x.f, 1/1)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::InsufficientPermission)),
        "expected InsufficientPermission, got {result:?}"
    );
}

#[test]
fn inline_exhale_unproven_fact_fails() {
    // The exhaled boolean `x.f == 5` is not known (nothing assumed it).
    let input = r#"
field f: Int

method m(x: Ref)
{
    inhale acc(x.f, 1/1)
    exhale x.f == 5
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::AssertionFailed)),
        "expected AssertionFailed, got {result:?}"
    );
}

#[test]
fn new_single_field_grants_full_permission() {
    let input = r#"
field f: Int

method m()
{
    var x: Ref := new(f)
    exhale acc(x.f, 1/1)
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "new(f) should grant full permission to x.f"
    );
}

#[test]
fn new_permission_is_exactly_full() {
    // `new(f)` grants exactly `1/1`; exhaling it twice over-consumes.
    let input = r#"
field f: Int

method m()
{
    var x: Ref := new(f)
    exhale acc(x.f, 1/1)
    exhale acc(x.f, 1/1)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::InsufficientPermission)),
        "expected InsufficientPermission, got {result:?}"
    );
}

#[test]
fn perm_in_exhale_sees_removed_permission() {
    // `acc(x.f)` is exhaled first, so `perm(x.f)` then reads `none` (0).
    let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 1/1)
{
    exhale acc(x.f, 1/1) && perm(x.f) == none
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "perm() in exhale must see the post-removal heap"
    );
}

#[test]
fn perm_before_acc_in_exhale_is_full() {
    // `perm(x.f)` is read before its `acc` is subtracted, so it is `write` (1).
    let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 1/1)
{
    exhale perm(x.f) == write && acc(x.f, 1/1)
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "perm() read before its acc must be full"
    );
}

#[test]
fn perm_in_inhale_sees_added_permission() {
    // Inhale tracks the growing heap: after `acc(x.f)`, `perm(x.f) == write`.
    let input = r#"
field f: Int

method m(x: Ref)
{
    inhale acc(x.f, 1/1) && perm(x.f) == write
    exhale acc(x.f, 1/1)
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "perm() in inhale must see the added permission"
    );
}

#[test]
fn exhale_value_read_uses_pre_exhale_heap() {
    // The value `x.f` is read in the same exhale that gives up `acc(x.f)`;
    // value reads resolve against the fixed pre-exhale heap, so it works.
    let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 1/1)
{
    inhale x.f == 5
    exhale acc(x.f, 1/1) && x.f == 5
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "value read in exhale must use the pre-exhale heap"
    );
}

#[test]
fn assert_held_permission_ok() {
    // `assert acc(x.f)` becomes `perm(x.f) >= write`; held in full → ok, and
    // it is non-destructive, so the permission is still exhalable after.
    let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 1/1)
{
    assert acc(x.f, 1/1)
    exhale acc(x.f, 1/1)
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "assert acc must hold and not consume the permission"
    );
}

#[test]
fn assert_unheld_permission_fails() {
    // `perm(x.f) = 0 >= write` is false.
    let input = r#"
field f: Int

method m(x: Ref)
{
    assert acc(x.f, 1/1)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::AssertionFailed)),
        "expected AssertionFailed, got {result:?}"
    );
}

#[test]
fn deref_without_permission_fails() {
    let input = r#"
field f: Int

method m(x: Ref)
{
    assert x.f == 5
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::InsufficientPermission)),
        "expected InsufficientPermission, got {result:?}"
    );
}

#[test]
fn assert_pure_unproven_fails() {
    let input = r#"
method m(x: Int)
{
    assert x == 5
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::AssertionFailed)),
        "expected AssertionFailed, got {result:?}"
    );
}

#[test]
fn assume_then_assert_pure() {
    let input = r#"
method m(x: Int)
{
    assume x == 5
    assert x == 5
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "assumed fact must be assertable"
    );
}

#[test]
fn assume_then_assert_acc() {
    // `assume acc(x.f)` records the fact `perm(x.f) >= write` (it adds no
    // chunk — unlike `inhale`); asserting the same fact then holds. The
    // permission is genuinely held here so the assumed fact is consistent.
    let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 1/1)
{
    assume acc(x.f, 1/1)
    assert acc(x.f, 1/1)
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "assumed perm fact must be assertable"
    );
}

#[test]
fn new_multiple_fields() {
    let input = r#"
field f: Int
field g: Int

method m()
{
    var x: Ref := new(f, g)
    exhale acc(x.f, 1/1) && acc(x.g, 1/1)
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "new(f, g) should grant full permission to both fields"
    );
}

#[test]
fn concrete_predicate_body_verifies() {
    // A predicate with a concrete body lowers to a resource and is verified
    // well-formed (reading `this.f` needs the `acc(this.f)` it just granted).
    let input = r#"
field f: Int

predicate number(this: Ref) {
    acc(this.f, 1/1) && this.f == 0
}
"#;
    let program = lower(input);
    assert!(
        verify_named_resource(&program, "number").is_ok(),
        "concrete predicate should verify well-formed"
    );
}

#[test]
fn graft_reuses_ensures_equality() {
    // `seteq`'s postcondition establishes `x.f == y.f`. The caller grafts the
    // certificate, assumes that boolean, and can then discharge the same
    // equality without re-deriving it.
    let input = r#"
field f: Int

method seteq(x: Ref, y: Ref)
    requires acc(x.f, 1/1) && acc(y.f, 1/1)
    ensures acc(x.f, 1/1) && acc(y.f, 1/1) && x.f == y.f

method m(x: Ref, y: Ref)
    requires acc(x.f, 1/1) && acc(y.f, 1/1)
{
    seteq(x, y)
    assert x.f == y.f
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "the grafted ensures equality should be reusable"
    );
}

#[test]
fn literal_division_folds_to_real() {
    // `4/2` is const-folded at translation to the Real literal `2/1`, so it
    // matches an explicit `2/1` on exhale.
    let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 4/2)
{
    exhale acc(x.f, 2/1)
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "4/2 should fold to 2/1 and match"
    );
}

#[test]
fn under_pc_verifies() {
    // `assume (b && true) ==> x.f == 10` then `assert (b && b) ==> x.f == 10`:
    // both antecedents collapse to `b`, so the implications are congruent.
    let input = r#"
field f: Int

method under_pc(x: Ref, b: Bool)
{
    inhale acc(x.f, 1/1)
    assume (b && true) ==> x.f == 10
    assert (b && b) ==> x.f == 10
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "under_pc").is_ok(),
        "under_pc should verify with the and-true / and-self rewrites"
    );
}

#[test]
fn unlabeled_old_reads_post_requires_heap() {
    // Unlabeled `old(...)` reads the post-requires-inhale heap. The
    // precondition holds `acc(x.f, 1/2)`; after inhaling another `1/2` the
    // current permission is `1/1`, but `old(perm(x.f))` must still see the
    // `1/2` held right after the precondition was inhaled.
    let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 1/2)
{
    inhale acc(x.f, 1/2)
    assert perm(x.f) == 1/1
    assert old(perm(x.f)) == 1/2
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "old(perm(x.f)) should see the 1/2 permission held after the precondition"
    );
}

#[test]
fn labeled_old_reads_label_heap_permission() {
    // `label L` captures the heap holding `acc(x.f, 1/2)`. After inhaling
    // another `1/2`, the current permission is `1/1`, but `old[L](perm(x.f))`
    // must still see the `1/2` held at `L` — proving `old[L]` reaches the
    // captured heap, not the current one.
    let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 1/2)
{
    label L
    inhale acc(x.f, 1/2)
    assert perm(x.f) == 1/1
    assert old[L](perm(x.f)) == 1/2
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "old[L](perm(x.f)) should see the 1/2 permission held at L"
    );
}

#[test]
fn old_before_its_label_is_a_translation_error() {
    // Straight-line lowering only knows labels it has already passed. An
    // `old[L]` used before `label L` cannot find the captured heap and is a
    // clean translation error (not a panic).
    let input = r#"
field f: Int

method m(x: Ref)
    requires acc(x.f, 1/1)
{
    assert old[L](x.f) == x.f
    label L
}
"#;
    let mut program = viper_parser::vpr_program(input).expect("parse");
    let mut ic = IdentCollector::default();
    program.walk_mut(&mut ic);
    let interner = ic.finalize();
    let mut gc = GlobalsCollector::new(&interner);
    program.walk(&mut gc);
    let globals = gc.finalize().expect("globals");
    disambiguate(&mut program, &interner, &globals).expect("disambiguation");
    inline_macros(&mut program, &interner).expect("macros");
    let typed = typecheck_program(&mut program, &interner, &globals).expect("typecheck");
    assert!(
        translate::translate(&typed, &interner, &globals).is_err(),
        "old[L] before label L must fail translation"
    );
}

// A conditional spatial assertion `b ? A : A'` lowers to one additive heap
// timeline with the branch folded into the permission fractions (no heap
// ternary). The verifier recovers each branch by assuming the condition.
const COND_INHALE: &str = r#"
field f: Int

method m(x: Ref, b: Bool)
{
    inhale b ? (acc(x.f, 1/2) && x.f == 0) : (acc(x.f, 1/1) && x.f == 1)
"#;

#[test]
fn conditional_inhale_true_branch_verifies() {
    let input =
        format!("{COND_INHALE}    assume b\n    assert perm(x.f) == 1/2\n    assert x.f == 0\n}}");
    let program = lower(&input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "under `b`, the held permission is 1/2 and x.f == 0"
    );
}

#[test]
fn conditional_inhale_false_branch_verifies() {
    // `b == false` (not `!b`): the e-graph propagates equality with a literal
    // via `eq-true-union`, whereas a `!b` ternary's negation isn't pushed
    // back onto `b` — a separate backend gap, not the branch lowering.
    let input = format!(
        "{COND_INHALE}    assume b == false\n    assert perm(x.f) == 1/1\n    assert x.f == 1\n}}"
    );
    let program = lower(&input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "under `!b`, the held permission is 1/1 and x.f == 1"
    );
}

#[test]
fn conditional_inhale_does_not_leak_other_branch() {
    // Under the true branch, the false branch's value (`x.f == 1`) must NOT
    // be derivable — the agreement axiom keeps the branch values isolated.
    let input = format!("{COND_INHALE}    assume b\n    assert x.f == 1\n}}");
    let program = lower(&input);
    assert!(
        matches!(
            verify_named_method(&program, "m"),
            Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)
        ),
        "true branch must not leak the false branch's value"
    );
}

#[test]
fn implies_spatial_verifies() {
    // `b ==> (acc(x.f) && x.f == 7)` gives full permission and the value
    // only under `b`; assuming `b`, both are recoverable.
    let input = r#"
field f: Int

method m(x: Ref, b: Bool)
{
    inhale b ==> (acc(x.f, 1/1) && x.f == 7)
    assume b
    assert perm(x.f) == 1/1
    assert x.f == 7
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "under `b`, the implication grants full permission and x.f == 7"
    );
}

#[test]
fn field_assign_updates_value() {
    // With write permission, `x.f := 10` mutates the heap value so a later
    // `assert x.f == 10` discharges.
    let input = r#"
field f: Int

method m(x: Ref)
{
    inhale acc(x.f, 1/1)
    x.f := 10
    assert x.f == 10
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "field assignment under write permission should verify"
    );
}

#[test]
fn field_assign_without_write_permission_fails() {
    // Only 1/2 held after the exhale: a field write needs full permission.
    let input = r#"
field f: Int

method m(x: Ref)
{
    inhale acc(x.f, 1/1)
    exhale acc(x.f, 1/2)
    x.f := 20
}
"#;
    let program = lower(input);
    assert!(
        matches!(
            verify_named_method(&program, "m"),
            Err(ref e) if matches!(e.root_cause(), VerifyError::InsufficientPermission)
        ),
        "field write without full permission must fail"
    );
}

#[test]
fn field_assign_with_no_permission_fails() {
    let input = r#"
field f: Int

method m(x: Ref)
{
    x.f := 1
}
"#;
    let program = lower(input);
    assert!(
        matches!(
            verify_named_method(&program, "m"),
            Err(ref e) if matches!(e.root_cause(), VerifyError::InsufficientPermission)
        ),
        "field write with no permission held must fail"
    );
}

// ============================================================================
// Nested & recursive predicates (fold & unfold)
//
// A predicate whose body holds another predicate instance — nested
// (`Outer{ Inner(x) }`) or recursive (`List{ .. List(this.next) }`) — is folded
// by consuming the already-held inner chunk as one opaque footprint slot (its
// value = the inner predicate's snapshot). Folding is NOT recursive: the inner
// instance must already be folded, and is never expanded here. So a
// nested-predicate slot is structurally identical to a field slot, and
// recursion works for free (the self-referential snapshot type is opaque).
// ============================================================================

/// A recursive linked-list predicate lowers through the whole pipeline without
/// error.
#[test]
fn recursive_predicate_lowers() {
    let input = r#"
field val: Int
field next: Ref
predicate List(this: Ref) {
  acc(this.val, write) && acc(this.next, write) &&
  (this.next != null ==> List(this.next))
}
"#;
    // Must not panic / error during parse → typecheck → translate.
    let _ = lower(input);
}

/// Base case: a recursive `List` whose tail is `null` has its inner-list slot
/// absent (`None`), so fold/unfold round-trips the two fields.
#[test]
fn recursive_predicate_base_case_roundtrip() {
    let input = r#"
field val: Int
field next: Ref
predicate List(this: Ref) {
  acc(this.val, write) && acc(this.next, write) &&
  (this.next != null ==> List(this.next))
}
method m(this: Ref)
  requires acc(this.val, write) && acc(this.next, write) && this.next == null
{
  this.val := 5
  fold acc(List(this), write)
  unfold acc(List(this), write)
  assert this.val == 5
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "base-case List fold/unfold round-trip should preserve this.val"
    );
}

/// Unfolding a held recursive `List(this)` opens it back into its footprint
/// (two fields + the conditional inner list), so the fields become readable.
#[test]
fn recursive_predicate_unfold_exposes_fields() {
    let input = r#"
field val: Int
field next: Ref
predicate List(this: Ref) {
  acc(this.val, write) && acc(this.next, write) &&
  (this.next != null ==> List(this.next))
}
method m(this: Ref)
  requires acc(List(this), write)
{
  unfold acc(List(this), write)
  this.val := 7
  assert this.val == 7
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "unfolding List(this) should expose its fields for read/write"
    );
}

/// Recursive one level: holding the fields plus the inner `List(this.next)`
/// (with `next != null`) lets `List(this)` fold — the inner list chunk moves
/// into the outer predicate.
#[test]
fn recursive_predicate_one_level_fold() {
    let input = r#"
field val: Int
field next: Ref
predicate List(this: Ref) {
  acc(this.val, write) && acc(this.next, write) &&
  (this.next != null ==> List(this.next))
}
method m(this: Ref)
  requires acc(this.val, write) && acc(this.next, write) &&
           this.next != null && acc(List(this.next), write)
{
  fold acc(List(this), write)
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "folding List(this) with a held inner List(this.next) should succeed"
    );
}

/// Nested non-recursive: `Outer{ Inner(x) }` round-trips through the held
/// `Inner(x)` chunk and recovers the inner field after both unfolds.
#[test]
fn nested_predicate_fold_unfold_roundtrip() {
    let input = r#"
field f: Int
predicate Inner(x: Ref) { acc(x.f, write) }
predicate Outer(x: Ref) { Inner(x) }
method m(x: Ref)
  requires acc(x.f, write)
{
  x.f := 5
  fold acc(Inner(x), write)
  fold acc(Outer(x), write)
  unfold acc(Outer(x), write)
  unfold acc(Inner(x), write)
  assert x.f == 5
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "Outer Inner(x) fold/unfold round-trip should recover x.f == 5"
    );
}

/// Folding `Outer(x)` consumes the inner `Inner(x)` chunk: unfolding `Inner(x)`
/// directly afterwards must fail for lack of permission (it moved into `Outer`).
#[test]
fn nested_predicate_fold_consumes_inner() {
    let input = r#"
field f: Int
predicate Inner(x: Ref) { acc(x.f, write) }
predicate Outer(x: Ref) { Inner(x) }
method m(x: Ref)
  requires acc(Inner(x), write)
{
  fold acc(Outer(x), write)
  unfold acc(Inner(x), write)
}
"#;
    let program = lower(input);
    assert!(
        matches!(
            verify_named_method(&program, "m"),
            Err(ref e) if matches!(e.root_cause(), VerifyError::InsufficientPermission)
        ),
        "unfolding Inner(x) after it was folded into Outer(x) must lack permission"
    );
}

#[test]
fn mutually_recursive_snapshots_verify() {
    // `A` and `B` reference each other only through a predicate *location*
    // (`acc(B(..))` / `acc(A(..))`), not fold/unfold — so neither is a
    // verification dependency of the other. Their snapshots are mutually
    // recursive (nominal, by id), which is allowed: both verify.
    let input = r#"
field f: Int
field nxt: Ref
predicate A(x: Ref) { acc(x.f, write) && acc(x.nxt, write) && (x.nxt != null ==> B(x.nxt)) }
predicate B(x: Ref) { acc(x.f, write) && acc(x.nxt, write) && (x.nxt != null ==> A(x.nxt)) }
"#;
    let program = lower(input);
    assert!(verify_named_resource(&program, "A").is_ok());
    assert!(verify_named_resource(&program, "B").is_ok());
}

#[test]
fn cyclic_unfolding_predicates_rejected() {
    // `P` unfolds `Q` and `Q` unfolds `P`: each appears in the other's body in
    // an *unfolding* context, so each is a verification dependency of the other
    // → a cycle, rejected by `analyze` (unlike the mutual-snapshot case above).
    let input = r#"
predicate P(x: Ref) { acc(Q(x), write) && (unfolding acc(Q(x), write) in true) }
predicate Q(x: Ref) { acc(P(x), write) && (unfolding acc(P(x), write) in true) }
"#;
    let program = lower(input);
    assert!(
        matches!(
            crate::vmir::analyze(program),
            Err(crate::vmir::AnalysisError::CircularDependency(_))
        ),
        "mutually-unfolding predicates should be a circular dependency"
    );
}
