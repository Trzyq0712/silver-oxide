//! End-to-end verification tests: lower a Silver source string through the
//! full pipeline (parse → … → translate) and verify, asserting pass/fail and
//! specific `VerifyError` variants. The e-graph unit tests stay in `super`'s
//! `mod tests`.

use std::sync::Arc;

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
    let typed = typecheck_program(&mut program, interner, &globals).expect("typecheck");
    // `Option` is a verifier builtin (the mono allocator registers it), not a
    // program declaration — nothing to inject here.
    translate::translate(&typed).expect("translate")
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

#[test]
fn ensures_resource_uses_precondition_facts() {
    // The `#ensures` resource body divides by `x`, which is only well-formed
    // because the precondition `x != 0` is grafted into the ctx slot and assumed
    // when the resource is verified self-contained. Without the `requires`, the
    // same division must be rejected.
    let with_req = r#"
method m(x: Int) returns (r: Int)
    requires x != 0
    ensures r == 100 / x
{ r := 100 / x }
"#;
    let program = lower(with_req);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "division in ensures should be safe given `requires x != 0`"
    );

    let without_req = r#"
method m(x: Int) returns (r: Int)
    ensures r == 100 / x
{ r := 100 / x }
"#;
    let program = lower(without_req);
    // Without a precondition the `#ensures` resource is self-framed and its
    // division has no nonzero witness — it fails as a resource.
    assert!(
        matches!(
            verify_named_resource(&program, "m#ensures"),
            Err(ref err) if matches!(err.root_cause(), VerifyError::SideCondition(_))
        ),
        "division in ensures must fail without a precondition framing the divisor"
    );
}

#[test]
fn old_in_ensures_reads_pre_state() {
    // `old(x.f)` reads the method pre-state. Untouched field: `x.f == old(x.f)`
    // holds. Mutated field: it must not.
    let unchanged = r#"
field f: Int
method m(x: Ref) returns (r: Int)
    requires acc(x.f, 1/1)
    ensures acc(x.f, 1/1) && x.f == old(x.f)
{ r := x.f }
"#;
    let program = lower(unchanged);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "untouched field equals its old value"
    );

    let mutated = r#"
field f: Int
method m(x: Ref)
    requires acc(x.f, 1/1)
    ensures acc(x.f, 1/1) && x.f == old(x.f)
{ x.f := 7 }
"#;
    let program = lower(mutated);
    assert!(
        verify_named_method(&program, "m").is_err(),
        "mutated field must not equal its old value"
    );
}

#[test]
fn old_over_heap_dependent_function_binds_pre_state() {
    // `old(get(this))` applies a heap-dependent function under `old`: the
    // ensures body reads the pre-state via `Snap` on the `FromSnap`-widened
    // snapshot parameter, which must congruence-collapse to the caller's real
    // pre-state values at the exhale graft (regression: the old `old_reads`
    // mechanism recorded only direct `Deref`s and left these unbound).
    let unchanged = r#"
field v: Int

predicate number(this: Ref) { acc(this.v) }

function get(this: Ref): Int
    requires number(this)
{ unfolding number(this) in this.v }

method keep(this: Ref)
    requires number(this)
    ensures number(this) && old(get(this)) == get(this)
{ }
"#;
    let program = lower(unchanged);
    assert!(
        verify_named_method(&program, "keep").is_ok(),
        "old(get(this)) must equal get(this) for an untouched predicate"
    );

    // Mutating the value under the predicate must break the equality.
    let mutated = r#"
field v: Int

predicate number(this: Ref) { acc(this.v) }

function get(this: Ref): Int
    requires number(this)
{ unfolding number(this) in this.v }

method bump(this: Ref)
    requires number(this)
    ensures number(this) && old(get(this)) == get(this)
{
    unfold number(this)
    this.v := this.v + 1
    fold number(this)
}
"#;
    let program = lower(mutated);
    assert!(
        verify_named_method(&program, "bump").is_err(),
        "old(get(this)) must not equal get(this) after mutating this.v"
    );
}

/// Verify the resource interned under `name`, panicking if it is missing or
/// is not a `Resource`.
fn verify_named_resource(program: &vmir::Program, name: &str) -> Result<(), VerifyError> {
    let id = program
        .id(name)
        .unwrap_or_else(|| panic!("missing resource {name}"));
    let vmir::Declaration::Resource(r) = &program.decls[id] else {
        panic!("{name} must be a Resource");
    };
    let mut alloc = crate::verify::func_registry::FuncRegistry::new(program);
    // Build certificates for the *other* resources (dependency order ≈ decl
    // order for these small fixtures), tolerating failures, so a body that
    // unfolds another predicate can graft its certificate. The target itself is
    // skipped so a deliberately-failing target still returns `Err`.
    let fn_certs = build_fn_certs(program, &mut alloc);
    let mut certs = HashMap::new();
    for (cid, decl) in program.decls.iter_enumerated() {
        if cid == id {
            continue;
        }
        if let vmir::Declaration::Resource(cr) = decl {
            let cname = program.name(cid).to_string();
            if let Ok(Some(cert)) =
                verify_resource(program, &cname, cr, &certs, &fn_certs, &mut alloc)
            {
                certs.insert(cid, cert);
            }
        }
    }
    verify_resource(program, name, r, &certs, &fn_certs, &mut alloc).map(|_| ())
}

/// Verify every function in `program` except `skip` (test helper), caching
/// certificates. Iterates to a fixpoint so callees are certified before callers
/// (a function whose ensures/callees aren't yet grafted fails and is retried on a
/// later pass) — the helper's stand-in for the driver's topological order.
/// Functions are heap-free and never call resources, so an empty resource-cert
/// map suffices.
fn build_fn_certs_except(
    program: &vmir::Program,
    skip: Option<MemberId>,
    alloc: &mut crate::verify::func_registry::FuncRegistry,
) -> HashMap<MemberId, Arc<FunctionDefinition>> {
    let no_certs = HashMap::new();
    let mut fn_certs = HashMap::new();
    loop {
        let mut progress = false;
        for (id, decl) in program.decls.iter_enumerated() {
            if Some(id) == skip || fn_certs.contains_key(&id) {
                continue;
            }
            if let vmir::Declaration::Function(f) = decl {
                let name = program.name(id).to_string();
                if let Ok(Some(cert)) =
                    verify_function(program, &name, id, f, &no_certs, &fn_certs, None, alloc)
                {
                    fn_certs.insert(id, cert);
                    progress = true;
                }
            }
        }
        if !progress {
            break;
        }
    }
    fn_certs
}

/// Verify every function in `program` (test helper). See [`build_fn_certs_except`].
fn build_fn_certs(
    program: &vmir::Program,
    alloc: &mut crate::verify::func_registry::FuncRegistry,
) -> HashMap<MemberId, Arc<FunctionDefinition>> {
    build_fn_certs_except(program, None, alloc)
}

/// Build certificates for every resource in `program` (test helper). Shares the
/// `alloc` so certificate ids match the method's later use.
fn build_certs(
    program: &vmir::Program,
    fn_certs: &HashMap<MemberId, Arc<FunctionDefinition>>,
    alloc: &mut crate::verify::func_registry::FuncRegistry,
) -> HashMap<MemberId, ResourceDefinition> {
    let mut certs = HashMap::new();
    for (id, decl) in program.decls.iter_enumerated() {
        if let vmir::Declaration::Resource(r) = decl {
            let name = program.name(id).to_string();
            if let Some(cert) = verify_resource(program, &name, r, &certs, fn_certs, alloc)
                .expect("resource verifies")
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

/// Jointly build resource and function certificates to a fixpoint (test
/// helper) — the stand-in for the driver's topological order when the two
/// kinds depend on each other: a heap-dependent function's body needs its
/// `f#requires` **Resource** cert (`FromSnap`), while a resource body may call
/// functions. Failures are tolerated (retried until no progress) so a
/// deliberately-failing member simply ends up without a cert.
#[allow(clippy::type_complexity)]
fn build_all_certs(
    program: &vmir::Program,
    alloc: &mut crate::verify::func_registry::FuncRegistry,
) -> (
    HashMap<MemberId, ResourceDefinition>,
    HashMap<MemberId, Arc<FunctionDefinition>>,
) {
    let mut certs = HashMap::new();
    let mut fn_certs = HashMap::new();
    loop {
        let mut progress = false;
        for (id, decl) in program.decls.iter_enumerated() {
            match decl {
                vmir::Declaration::Resource(r) if !certs.contains_key(&id) => {
                    let name = program.name(id).to_string();
                    if let Ok(Some(cert)) =
                        verify_resource(program, &name, r, &certs, &fn_certs, alloc)
                    {
                        certs.insert(id, cert);
                        progress = true;
                    }
                }
                vmir::Declaration::Function(f) if !fn_certs.contains_key(&id) => {
                    let name = program.name(id).to_string();
                    if let Ok(Some(cert)) =
                        verify_function(program, &name, id, f, &certs, &fn_certs, None, alloc)
                    {
                        fn_certs.insert(id, cert);
                        progress = true;
                    }
                }
                _ => {}
            }
        }
        if !progress {
            break;
        }
    }
    (certs, fn_certs)
}

/// Verify the method `name`, panicking if missing or not a `Method`.
fn verify_named_method(program: &vmir::Program, name: &str) -> Result<(), VerifyError> {
    let id = program
        .id(name)
        .unwrap_or_else(|| panic!("missing method {name}"));
    let vmir::Declaration::Method(m) = &program.decls[id] else {
        panic!("{name} must be a Method");
    };
    let mut alloc = crate::verify::func_registry::FuncRegistry::new(program);
    let (certs, fn_certs) = build_all_certs(program, &mut alloc);
    verify_method(program, name, m, &certs, &fn_certs, &mut alloc)
}

/// Verify the function `name` with all other members' certs built (test
/// helper for heap-dependent functions, which need their `#requires` Resource
/// cert).
fn verify_named_function(program: &vmir::Program, name: &str) -> Result<(), VerifyError> {
    let id = program
        .id(name)
        .unwrap_or_else(|| panic!("missing function {name}"));
    let vmir::Declaration::Function(f) = &program.decls[id] else {
        panic!("{name} must be a Function");
    };
    let mut alloc = crate::verify::func_registry::FuncRegistry::new(program);
    let (certs, mut fn_certs) = build_all_certs(program, &mut alloc);
    // Re-verify the target itself so a failing target returns its `Err` (the
    // fixpoint helper swallowed it).
    fn_certs.remove(&id);
    verify_function(program, name, id, f, &certs, &fn_certs, None, &mut alloc).map(|_| ())
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
    // A user-written generic ADT used at two element types. The e-graph is
    // polymorphic: `Box[Int]` and `Box[Bool]` share one `mk` constructor id but
    // carry distinct `Ty` type-arg children, so congruence keeps the two
    // projections disjoint (`bi.v == 5`, `bb.v == true` never merge).
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
fn domain_function_call_is_pure_and_congruent() {
    // A domain function is uninterpreted but a *function*: two syntactically
    // identical calls land in one e-class by congruence, so `f(3) == f(3)`
    // verifies. (Exercises the pure `DomainFunctionCall` lowering path — a
    // domain call must reach the pure node, not the heap `FunctionCall`.)
    let input = r#"
domain D { function f(x: Int): Int }
method m()
{
    assert f(3) == f(3)
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "f(3) == f(3) should verify by congruence"
    );
}

#[test]
fn domain_function_distinct_args_do_not_merge() {
    // Uninterpreted: `f(3)` and `f(4)` have distinct argument enodes, so they
    // are not provably equal — asserting their equality must fail.
    let input = r#"
domain D { function f(x: Int): Int }
method m()
{
    assert f(3) == f(4)
}
"#;
    let program = lower(input);
    assert!(
        matches!(
            verify_named_method(&program, "m"),
            Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)
        ),
        "f(3) == f(4) should fail"
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
fn ensures_equality_is_reusable_at_call_site() {
    // `seteq`'s postcondition establishes `x.f == y.f`. The caller rebuilds the
    // ensures recipe, assumes that boolean, and can then discharge the same
    // equality.
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
    let typed = typecheck_program(&mut program, interner, &globals).expect("typecheck");
    assert!(
        translate::translate(&typed).is_err(),
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

#[test]
fn function_body_inlined_when_spec_insufficient() {
    // The spec (`result >= 0`) alone can't prove `five() == 5`; only the grafted
    // body definition (`five() == 5`) discharges the assert.
    let input = r#"
function five(): Int
    ensures result >= 0
{ 5 }

method m()
{
    assert five() == 5
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "grafted function body should discharge `five() == 5`"
    );
}

#[test]
fn chained_function_bodies_inlined() {
    // `six` calls `five`; proving `six() == 6` needs both bodies inlined.
    let input = r#"
function five(): Int { 5 }
function six(): Int { five() + 1 }

method m()
{
    assert six() == 6
}
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "chained function bodies should inline to prove `six() == 6`"
    );
}

#[test]
fn function_postcondition_discharged_by_body() {
    // The exit `assert inc#ensures(x, result)` is discharged via the grafted
    // `inc#ensures` definition against the body result `x + 1`.
    let input = r#"
function inc(x: Int): Int
    ensures result == x + 1
{ x + 1 }
"#;
    let program = lower(input);
    assert!(
        verify_named_function(&program, "inc").is_ok(),
        "function whose ensures follows from its body should verify"
    );
}

#[test]
fn recursive_function_accepted_as_scc() {
    // A self-recursive function is a self-looping singleton SCC → `analyze` now
    // accepts it (limited-function encoding) rather than rejecting the cycle, and
    // marks it recursive so its calls route through the limited twin.
    let input = r#"
function loop(x: Int): Int { loop(x) }
"#;
    let program = lower(input);
    let loop_id = program.id("loop").expect("loop function");
    let analyzed = crate::vmir::analyze(program).expect("function recursion is accepted");
    assert_eq!(
        analyzed.recursive_scc(loop_id),
        Some(std::collections::HashSet::from([loop_id])),
        "self-recursive function should be its own recursive SCC"
    );
}

#[test]
fn heap_dep_function_verifies_and_defines_at_call_site() {
    // The full snapshot-passing pipeline: the call site's `Snap` checks the
    // precondition (footprint + bool) against the caller heap, the callee's
    // cert (verified against `H(s)`) grafts as `get(y, s) == unwrap(proj_0(s))`,
    // and `s = cons(Some(y.f))` collapses it to the caller's chunk value — so
    // `a == y.f` proves without any postcondition.
    let input = r#"
field f: Int

function get(x: Ref): Int
    requires acc(x.f) && x.f > 0
    ensures result == x.f
{ x.f }

method m(y: Ref)
    requires acc(y.f) && y.f > 0
{
    var a: Int := get(y)
    assert a > 0
    assert a == y.f
}
"#;
    let program = lower(input);
    assert!(
        verify_named_function(&program, "get").is_ok(),
        "heap-dep function must verify (body framed by H(s), ensures from body)"
    );
    let result = verify_named_method(&program, "m");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn heap_dep_call_without_permission_fails() {
    // `m` holds no permission to `y.f`: the call-site `Snap`'s footprint
    // sufficiency check fails.
    let input = r#"
field f: Int

function get(x: Ref): Int
    requires acc(x.f)
{ x.f }

method m(y: Ref)
{
    var a: Int := get(y)
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
fn heap_dep_call_precondition_bool_fails() {
    // `m` holds the footprint but cannot prove the precondition's pure fact
    // (`y.f > 0`): the `Snap`'s implicit bool assert fails.
    let input = r#"
field f: Int

function get(x: Ref): Int
    requires acc(x.f) && x.f > 0
{ x.f }

method m(y: Ref)
    requires acc(y.f)
{
    var a: Int := get(y)
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
fn heap_dep_body_read_outside_footprint_fails() {
    // The body reads `x.g` but the precondition only grants `x.f`: the deref
    // is not framed by the reconstructed `H(s)`.
    let input = r#"
field f: Int
field g: Int

function get(x: Ref): Int
    requires acc(x.f)
{ x.g }
"#;
    let program = lower(input);
    let result = verify_named_function(&program, "get");
    assert!(
        matches!(result, Err(ref err) if matches!(err.root_cause(), VerifyError::InsufficientPermission)),
        "expected InsufficientPermission, got {result:?}"
    );
}

#[test]
fn heap_dep_calls_frame_across_unrelated_write() {
    // Two calls on either side of a write to an *unrelated* field: the `f`
    // chunk value is unchanged, so both `Snap`s build the same `cons` and the
    // two applications are congruent — snapshot-passing gives heap framing for
    // free.
    let input = r#"
field f: Int
field g: Int

function get(x: Ref): Int
    requires acc(x.f)
{ x.f }

method m(y: Ref)
    requires acc(y.f) && acc(y.g)
{
    var a: Int := get(y)
    y.g := 5
    var b: Int := get(y)
    assert a == b
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn heap_dep_heap_reading_ensures_consumed_at_call_site() {
    // KNOWN LIMITATION (postconditions disabled): the postcondition itself
    // reads the heap (`result == x.f`). With an abstract (bodyless) heap-dep
    // function, `get#ensures` was previously the call site's *only* source of
    // information about the result — but postcondition stitching (both the
    // use-side assume and the body's own exit assert) is disabled for now
    // (see `translate::pure_exp::lower_func_app`/`lower_function_body`), so
    // the call site no longer learns `ret == y.f` and the assert fails.
    let input = r#"
field f: Int

function get(x: Ref): Int
    requires acc(x.f)
    ensures result == x.f

method m(y: Ref)
    requires acc(y.f)
{
    var a: Int := get(y)
    assert a == y.f
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)),
        "expected AssertionFailed (postconditions disabled), got {result:?}"
    );
}

// ---- Domain axioms ---------------------------------------------------------

#[test]
fn ground_axiom_discharges_assert() {
    // `size()` is uninterpreted; only the axiom pins its value.
    let input = r#"
domain D {
    function size(): Int
    axiom sz { size() == 0 }
}
method client() {
    assert size() == 0
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn ground_axiom_over_abstract_silver_function() {
    // `f` is an abstract (bodyless, contractless) Silver function — the axiom
    // is the only source of `f() == 42`.
    let input = r#"
function f(): Int
domain D {
    axiom a { f() == 42 }
}
method client() {
    assert f() == 42
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn unbacked_assert_still_fails_with_axioms_present() {
    // Negative control: the axiom pins `f`, not `g` — asserting about `g`
    // must still fail.
    let input = r#"
function f(): Int
function g(): Int
domain D {
    axiom a { f() == 42 }
}
method client() {
    assert g() == 42
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)),
        "expected AssertionFailed, got {result:?}"
    );
}

#[test]
fn generic_axiom_instantiates_at_use_site() {
    // The axiom is generic over T; `client` grounds it at `Int` through the
    // annotated local. The lazy rule fires on the `nil[Int]()` application,
    // instantiates `len(nil()) == 0` at Int, and congruence closes the goal.
    let input = r#"
domain List[T] {
    function nil(): List[T]
    function len(xs: List[T]): Int
    axiom { len(nil()) == 0 }
}
method client() {
    var l: List[Int] := nil()
    assert len(l) == 0
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn generic_axiom_two_instantiations_in_one_unit() {
    let input = r#"
domain List[T] {
    function nil(): List[T]
    function len(xs: List[T]): Int
    axiom { len(nil()) == 0 }
}
method client() {
    var l: List[Int] := nil()
    var m: List[Bool] := nil()
    assert len(l) == 0
    assert len(m) == 0
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn axiom_body_is_never_verified() {
    // The axiom divides by zero; axioms are trusted (no well-definedness
    // obligations), so an unrelated method still verifies.
    let input = r#"
domain D {
    function w(): Int
    axiom bad { w() == 1 / 0 }
}
method client() {
    assert true
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn ground_axiom_available_in_function_bodies() {
    // Axioms are assumed in every unit, not just methods: the function body's
    // exit `assert f#ensures` needs the axiom.
    let input = r#"
domain D {
    function size(): Int
    axiom sz { size() == 0 }
}
function probe(): Int
    ensures result == 0
{
    size()
}
"#;
    let program = lower(input);
    let result = verify_named_function(&program, "probe");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn generic_axiom_monomorphic_conjunct_not_yet_split() {
    // KNOWN DIVERGENCE (documented, fix deferred): the axiom is generic over T
    // (via `mk`), so the whole body — including the monomorphic conjunct
    // `tag() == 7` — sits behind the `mk[T]` trigger, and `client` never
    // applies `mk`. Silicon happens to pass this variant only because
    // `ground()` defaults `tag()`'s unconstrained T to Ref at the call site,
    // minting a D[Ref] occurrence that instantiates the axiom (and fails the
    // variant with `tag` declared outside the domain). Planned fix: split
    // top-level `&&` conjuncts into separate axioms (sound — types are
    // non-empty, so ∀T distributes over ∧), making this conjunct ground.
    let input = r#"
domain D[T] {
    function mk(): D[T]
    function tag(): Int
    axiom { mk() == mk() && tag() == 7 }
}
method client() {
    assert tag() == 7
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)),
        "documents the current divergence; if this starts passing, conjunct \
         splitting (or equivalent) landed — update this test to assert Ok"
    );
}

// ---- Pure `forall` quantifiers (v1: domain axioms, no Tier-4) --------------

#[test]
fn quantifier_basic() {
    // A bare `forall` axiom: the occurrence is unioned `true` directly, so the
    // trigger application `foo(7)` releases `foo(7) == true`.
    let input = r#"
domain D {
    function foo(i: Int): Bool
    axiom basic { forall i: Int :: {foo(i)} foo(i) }
}
method m() {
    assert foo(7)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn quantifier_multivar() {
    // Two binders, positional σ read off the two-argument trigger.
    let input = r#"
domain D {
    function bar(i: Int, j: Int): Bool
    axiom mv { forall i: Int, j: Int :: {bar(i, j)} bar(i, j) }
}
method m() {
    assert bar(3, 4)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn quantifier_guarded_concrete() {
    // Guarded `forall`: with `b()` concretely true, const-fold collapses the
    // guard `Ite(b(), Q, true)` to `Q = true`, releasing the instance. No
    // Tier-4 case-split needed.
    let input = r#"
domain D {
    function foo(i: Int): Bool
    function b(): Bool
    axiom g { b() ? (forall i: Int :: {foo(i)} foo(i)) : true }
}
method m() {
    inhale b()
    assert foo(7)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn quantifier_guard_stuck_fails() {
    // Guarded `forall` with `b()` unknown: the guard never collapses, so the
    // instance stays gated and `foo(0)` is unprovable. (Soundness: the guard
    // must not leak.)
    let input = r#"
domain D {
    function foo(i: Int): Bool
    function b(): Bool
    axiom g { b() ? (forall i: Int :: {foo(i)} foo(i)) : true }
}
method m() {
    assert foo(0)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)),
        "expected AssertionFailed, got {result:?}"
    );
}

#[test]
fn quantifier_wrong_instance_fails() {
    // The body is `i > 0 ==> foo(i)`. At the instance i := 0 it is
    // `Ite(false, foo(0), true) = true` — vacuously true, yielding nothing
    // about `foo(0)`. (Soundness: σ must be exact.)
    let input = r#"
domain D {
    function foo(i: Int): Bool
    axiom w { forall i: Int :: {foo(i)} i > 0 ==> foo(i) }
}
method m() {
    assert foo(0)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)),
        "expected AssertionFailed, got {result:?}"
    );
}

#[test]
fn quantifier_guarded_implication_not_yet() {
    // KNOWN LIMITATION (no Tier-4): proving `b() ==> foo(7)` needs a
    // goal-directed case-split on `b()` to collapse the guard `Ite(b(), Q,
    // true)` and then `Ite(Q, foo(7), true)`. Without Tier-4 neither guard
    // collapses (nothing concrete), so this fails. Flip to `is_ok` when Tier-4
    // lands.
    let input = r#"
domain D {
    function foo(i: Int): Bool
    function b(): Bool
    axiom g { b() ? (forall i: Int :: {foo(i)} foo(i)) : true }
}
method m() {
    assert b() ==> foo(7)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)),
        "documents the no-Tier-4 limitation; if this starts passing, \
         goal-directed ITE case-splitting landed — flip to assert Ok"
    );
}

#[test]
fn nested_quantifier_cascade() {
    // Nested `forall`: mentioning `f(1)` instantiates the outer quantifier at
    // i := 1, which materializes the inner occurrence `Q_inner(1)` (and merges
    // it `true` via the collapsed outer guard); the ground `g(1, 2)` then
    // matches the inner trigger `{g(i, j)}` — capture position 0 equals the
    // occurrence's capture 1 — releasing `g(1, 2) == true`.
    let input = r#"
domain D {
    function f(i: Int): Bool
    function g(i: Int, j: Int): Bool
    axiom nest { forall i: Int :: {f(i)} (forall j: Int :: {g(i, j)} g(i, j)) }
}
method m() {
    inhale f(1)
    assert g(1, 2)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn nested_quantifier_outer_untriggered_fails() {
    // Without any `f(..)` application the outer quantifier never instantiates,
    // so the inner occurrence is never materialized — `g(1, 2)` stays unknown
    // even though its own trigger is ground. (Soundness: no instantiation
    // without an occurrence.)
    let input = r#"
domain D {
    function f(i: Int): Bool
    function g(i: Int, j: Int): Bool
    axiom nest { forall i: Int :: {f(i)} (forall j: Int :: {g(i, j)} g(i, j)) }
}
method m() {
    assert g(1, 2)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)),
        "expected AssertionFailed, got {result:?}"
    );
}

#[test]
fn nested_quantifier_capture_mismatch_fails() {
    // The only materialized inner occurrence is `Q_inner(1)` (from `f(1)`), but
    // `g(2, 3)`'s capture position carries 2 ≠ 1 — the pair must be skipped, so
    // nothing is learned about `g(2, 3)`. (Soundness: capture positions must
    // e-match the occurrence's capture args.)
    let input = r#"
domain D {
    function f(i: Int): Bool
    function g(i: Int, j: Int): Bool
    axiom nest { forall i: Int :: {f(i)} (forall j: Int :: {g(i, j)} g(i, j)) }
}
method m() {
    inhale f(1)
    assert g(2, 3)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)),
        "expected AssertionFailed, got {result:?}"
    );
}

// ---- Pure `forall` quantifiers (v3: method bodies) --------------------------

#[test]
fn method_inhale_forall_instantiates() {
    // A `forall` inhaled in a method body: the occurrence is assumed true, so
    // the ground `foo(7)` triggers an instance and the assert discharges.
    let input = r#"
domain D { function foo(i: Int): Bool }
method client() {
    inhale forall i: Int :: {foo(i)} foo(i)
    assert foo(7)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn function_unfold_exposes_trigger_for_quantifier() {
    // `wrap`'s body is a bare `foo(x)` call — its certificate is captured raw
    // (unsaturated) and consumed lazily by its own `function_rule`, so
    // unfolding `wrap(7)` must expose a *literal* `foo(7)` occurrence for the
    // quantifier rule (also chained into the same saturation) to key off of,
    // in the same pass, not something a pre-emptive simplification erased.
    let input = r#"
domain D { function foo(i: Int): Bool }
function wrap(x: Int): Bool
{
    foo(x)
}
method client() {
    inhale forall i: Int :: {foo(i)} foo(i)
    assert wrap(7)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn method_inhale_forall_captures_local() {
    // The quantifier captures a method local; instantiation must match the
    // occurrence's capture argument.
    let input = r#"
domain D { function g(a: Int, i: Int): Bool }
method client(x: Int) {
    var l: Int := x
    inhale forall i: Int :: {g(l, i)} g(l, i)
    assert g(x, 3)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn method_inhale_forall_capture_mismatch_fails() {
    // Only `Q(x)` is inhaled — `g(y, 3)` has capture y ≠ x, so nothing is
    // learned about it. (Soundness: captures gate instantiation.)
    let input = r#"
domain D { function g(a: Int, i: Int): Bool }
method client(x: Int, y: Int) {
    inhale forall i: Int :: {g(x, i)} g(x, i)
    assert g(y, 3)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)),
        "expected AssertionFailed, got {result:?}"
    );
}

#[test]
fn method_inhale_forall_under_conjunction() {
    // The occurrence sits under a spatial `&&`: inhale-truth must decompose
    // down to the occurrence (and the pure left conjunct).
    let input = r#"
domain D { function foo(i: Int): Bool }
method client(x: Int) {
    inhale x > 0 && (forall i: Int :: {foo(i)} foo(i))
    assert foo(2) && x > 0
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn method_assert_forall_fails_gracefully() {
    // Proving a `forall` goal is out of scope: the occurrence never merges
    // `true`, so the assert fails cleanly (no crash, no unsound success).
    let input = r#"
domain D { function foo(i: Int): Bool }
method client() {
    inhale foo(1)
    assert forall i: Int :: {foo(i)} foo(i)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)),
        "expected AssertionFailed, got {result:?}"
    );
}

#[test]
fn method_inhale_forall_two_instantiations() {
    // One inhaled quantifier feeds two distinct ground instances in the same
    // unit.
    let input = r#"
domain D { function foo(i: Int): Bool }
method client() {
    inhale forall i: Int :: {foo(i)} foo(i)
    assert foo(1) && foo(2)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

// ---- Pure `forall` quantifiers (v3: contracts + predicate bodies) ----------

#[test]
fn method_requires_forall_usable_in_body() {
    // The entry inhale of `m#requires` assumes the resource bool — the
    // occurrence — so the body can instantiate it.
    let input = r#"
domain D { function g(a: Int, i: Int): Bool }
method m(x: Int)
    requires forall i: Int :: {g(x, i)} g(x, i)
{
    assert g(x, 42)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn callee_ensures_forall_inhaled_at_call_site() {
    // The call inhales `producer#ensures`, assuming its occurrence; the caller
    // then instantiates it.
    let input = r#"
domain D { function foo(i: Int): Bool }
method producer()
    ensures forall i: Int :: {foo(i)} foo(i)
method client() {
    producer()
    assert foo(5)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "client");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn method_ensures_forall_not_provable_from_requires_twin() {
    // KNOWN LIMITATION: the same syntactic `forall` in requires and ensures
    // lowers to two distinct Quantifier decls; the exit exhale must prove the
    // *ensures* occurrence, which nothing merges `true`. Proving foralls is
    // out of scope — this documents the graceful failure.
    let input = r#"
domain D { function foo(i: Int): Bool }
method m()
    requires forall i: Int :: {foo(i)} foo(i)
    ensures forall i: Int :: {foo(i)} foo(i)
{
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)),
        "expected AssertionFailed (proving foralls unsupported), got {result:?}"
    );
}

#[test]
fn predicate_body_forall_released_by_unfold() {
    // Unfolding the predicate assumes its body bool — the conjunction of the
    // guard and the occurrence — releasing both.
    let input = r#"
domain D { function g(a: Int, i: Int): Bool }
predicate P(i: Int) { i != 0 && (forall x: Int :: {g(i, x)} g(i, x)) }
method m(i: Int)
    requires P(i)
{
    unfold P(i)
    assert g(i, 3) && i != 0
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn function_requires_forall_usable_in_body() {
    // Heap-free function: the body assumes `f#requires(params)`; the contract
    // function's grafted definition equates that with the occurrence, so the
    // body can instantiate the quantifier to discharge the ensures.
    let input = r#"
domain D { function g(a: Int, i: Int): Bool }
function f(x: Int): Bool
    requires forall i: Int :: {g(x, i)} g(x, i)
    ensures result
{
    g(x, 1)
}
"#;
    let program = lower(input);
    let result = verify_named_function(&program, "f");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn function_requires_forall_call_site_unprovable() {
    // KNOWN LIMITATION (twin decls): the caller's inhaled `forall` and the
    // callee's `#requires` occurrence are distinct Quantifier decls, so the
    // call-site `assert f#requires(args)` cannot be discharged. Graceful
    // failure, same as any forall-proving goal.
    let input = r#"
domain D { function g(a: Int, i: Int): Bool }
function f(x: Int): Bool
    requires forall i: Int :: {g(x, i)} g(x, i)
{
    g(x, 1)
}
method m(x: Int) {
    inhale forall i: Int :: {g(x, i)} g(x, i)
    inhale f(x)
    assert g(x, 1)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)),
        "expected AssertionFailed (twin-decl limitation), got {result:?}"
    );
}

#[test]
fn function_ensures_forall_assumed_at_call_site() {
    // `f` is abstract (no body): its postcondition arrives via the synthesized
    // post axiom (`f#ensures(f())` — no requires, so unguarded), whose unfold
    // exposes the quantified fact; the trigger `foo(9)` then instantiates it.
    let input = r#"
domain D { function foo(i: Int): Bool }
function f(): Int
    ensures forall i: Int :: {foo(i)} foo(i)
method m() {
    var r: Int := f()
    assert foo(9)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        result.is_ok(),
        "abstract function's post axiom should deliver the forall; got {result:?}"
    );
}

#[test]
fn division_by_zero_in_function_body_fails() {
    // Instruction side conditions (`inst_obligations`) must be discharged in a
    // *function* body, not just a resource body: a literal zero divisor is a
    // verification failure, not a silently-accepted term.
    let input = r#"
function fdiv(a: Int): Int
{ a / 0 }
"#;
    let program = lower(input);
    let result = verify_named_function(&program, "fdiv");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::SideCondition("divisor may be zero"))),
        "expected SideCondition(divisor), got {result:?}"
    );
}

#[test]
fn division_by_zero_in_method_body_fails() {
    // Same obligation in a method body.
    let input = r#"
method mdiv(a: Int) {
    var x: Int := a / 0
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "mdiv");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::SideCondition("divisor may be zero"))),
        "expected SideCondition(divisor), got {result:?}"
    );
}

#[test]
fn division_by_provably_nonzero_divisor_verifies() {
    // The divisor obligation is discharged from the precondition, and the `1/0`
    // on the dead ternary arm is discharged by its (false) path condition —
    // together these pin that the new check is not vacuously failing.
    let input = r#"
method mok(a: Int)
    requires a != 0
{
    var x: Int := 10 / a
    var y: Int := (true ? 1 : 1 / 0)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "mok");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn modulo_by_zero_in_method_body_fails() {
    let input = r#"
method mmod(a: Int) {
    var x: Int := a % 0
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "mmod");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::SideCondition("divisor may be zero"))),
        "expected SideCondition(divisor), got {result:?}"
    );
}

#[test]
fn modulo_by_provably_nonzero_divisor_verifies() {
    let input = r#"
method mok(a: Int)
    requires a != 0
{
    var x: Int := 10 % a
    var y: Int := (true ? 1 : 1 % 0)
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "mok");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

#[test]
fn conditional_inhale_permission_is_nonnegative() {
    // CFG linearization encodes the guarded `inhale` as a scaled permission
    // `c ? 1/1 : 0/1`, so the permission ≥ 0 obligation — now also checked in
    // method bodies — is a `<` over an `ite`. `lt-ite` distributes it.
    let input = r#"
predicate number(this: Ref)

method give(this: Ref)
    ensures number(this)

method m(c: Bool, this: Ref)
{
    if (c) { give(this) } else { }
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(result.is_ok(), "expected Ok, got {result:?}");
}

// --- Phase 1: assumes are guarded by the path condition (Finding A) ----------

#[test]
fn conditional_inhale_bool_does_not_leak_past_its_branch() {
    // `give`'s `ensures x > 0` is inhaled only on the `c` arm, so `x > 0` must
    // NOT hold at the unconditional `assert` after the `if`. Before guarding the
    // inhaled bool (by `0 < perm`), the bool was unioned with `true`
    // unconditionally and this verified unsoundly.
    let input = r#"
method give(x: Int) ensures x > 0
method m(c: Bool, x: Int) {
    if (c) { give(x) }
    assert x > 0
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)),
        "expected AssertionFailed (inhaled bool must not leak past its branch), got {result:?}"
    );
}

#[test]
fn conditional_assume_does_not_leak_past_its_branch() {
    // The same, one level down: a bare `assume` inside a branch holds only on
    // that branch. `InstKind::Assume` used to ignore `inst.pc`.
    let input = r#"
method n(c: Bool, x: Int) {
    if (c) { assume x > 0 }
    assert x > 0
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "n");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)),
        "expected AssertionFailed (assume must not leak past its branch), got {result:?}"
    );
}

#[test]
fn unconditional_inhale_bool_is_still_assumed() {
    // Guarding must not break the common case: a straight-line inhale (perm
    // `1/1`, guard `0 < 1` folds to `true`) still assumes its bool.
    let input = r#"
method give(x: Int) ensures x > 0
method p1(x: Int) { give(x)  assert x > 0 }
"#;
    let program = lower(input);
    assert!(verify_named_method(&program, "p1").is_ok());
}

#[test]
fn assert_under_the_same_guard_that_assumed_it_holds() {
    // `assume` and `assert` under the same branch guard: the implication
    // `c ⇒ x>0` discharges the goal `x>0` under pc `c` (both share the literal).
    let input = r#"
method p3(c: Bool, x: Int) { if (c) { assume x > 0  assert x > 0 } }
"#;
    let program = lower(input);
    assert!(verify_named_method(&program, "p3").is_ok());
}

#[test]
fn both_arms_establishing_a_fact_needs_a_case_split_we_lack() {
    // KNOWN INCOMPLETENESS (not unsoundness). Both arms inhale `x > 0`, so it
    // genuinely holds at the merge — Silicon proves this. We record `c ⇒ x>0`
    // and `¬c ⇒ x>0`; recombining them into `x>0` needs a `c ∨ ¬c` case split
    // the e-graph does not perform. Before Phase 1 this verified, but only via
    // the same unsound unconditional union that made the leak tests pass. Flip
    // this assertion once branch joins or the Z3 fallback land.
    let input = r#"
method give(x: Int) ensures x > 0
method p2(c: Bool, x: Int) { if (c) { give(x) } else { give(x) }  assert x > 0 }
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "p2");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)),
        "expected AssertionFailed (case-split incompleteness); if this now verifies, \
         branch joins improved — flip the assertion. Got {result:?}"
    );
}

// --- Phase 3: function definitions are purified recipes, not e-graph grafts ---

#[test]
fn function_definition_does_not_leak_precondition_into_call_site() {
    // Finding B. `f`'s body has a divisor obligation (`g(x)/g(x)`) discharged from
    // `requires g(x) == 5`, so verifying `f` saturates `g(x) ≡ 5` into its e-graph.
    // The OLD certificate cloned that e-graph and `transplant`ed it, installing
    // `g(3) ≡ 5` unconditionally when `f(3)` unfolds (the rule is pc-blind), so the
    // empty-pc `assert g(3) == 5` passed even though `m` never establishes it. A
    // purified recipe imports no e-classes, so the merge cannot ride along.
    let input = r#"
function g(x: Int): Int
function f(x: Int): Int requires g(x) == 5 { g(x) / g(x) }
method m(b: Bool) {
  if (b) { assume g(3) == 5  var y: Int := f(3) }
  assert g(3) == 5
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        matches!(result, Err(ref e) if matches!(e.root_cause(), VerifyError::AssertionFailed)),
        "expected AssertionFailed (precondition must not leak from the function \
         definition); got {result:?}"
    );
}

#[test]
fn purified_function_definition_still_defines_the_body() {
    // The recipe must still install `f(a) == body`: `f(x) { x + 1 }` unfolds so
    // that `assert f(2) == 3` holds. (Guards nothing here — total function.)
    let input = r#"
function f(x: Int): Int { x + 1 }
method m() { assert f(2) == 3 }
"#;
    let program = lower(input);
    assert!(
        verify_named_method(&program, "m").is_ok(),
        "purified function definition should still discharge f(2) == 3"
    );
}

#[test]
fn heap_dependent_function_purifies_to_snapshot_projection() {
    // A heap-dependent body (`FromSnap`; `Deref`) purifies to `unwrap(proj_0(s))`.
    // The function verifies (frames its precondition footprint) end to end.
    let input = r#"
field f: Int
function get(x: Ref): Int requires acc(x.f) { x.f }
"#;
    let program = lower(input);
    assert!(
        verify_named_function(&program, "get").is_ok(),
        "heap-dependent function should verify with the purified recipe"
    );
}

// --- Function contracts as guarded rewrites (posts delivered transitively) ---

#[test]
fn abstract_function_post_available_at_call_site() {
    // `foo` is abstract: nothing about it used to survive outside the
    // (removed) immediate call-site assume. Its post now arrives via the
    // synthesized guarded axiom `foo#requires(x) ⟹ foo#ensures(x, foo(x))`,
    // whose guard the call-site `assert foo#requires(x)` establishes.
    let input = r#"
function foo(x: Int): Int
    requires x != 0
    ensures result == 10

method m(x: Int)
    requires x != 0
{
    assert foo(x) == 10
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        result.is_ok(),
        "abstract post should deliver; got {result:?}"
    );
}

#[test]
fn function_post_propagates_transitively() {
    // `m` never calls `mk`/`foo` directly — their applications only appear by
    // unfolding `g`'s body. `mk`'s (abstract, unguarded) post gives
    // `ok(mk(x))`; `foo`'s guarded post then fires (its defined pre-token
    // `foo#requires(mk(x))` unfolds to `ok(mk(x))`), yielding
    // `foo(mk(x)) == 10` and so `g(x) == 11`. Pure occurrence-keyed rewrites,
    // no call-site stitching anywhere in `m`.
    let input = r#"
domain D { function ok(y: Int): Bool }

function mk(x: Int): Int
    ensures ok(result)

function foo(y: Int): Int
    requires ok(y)
    ensures result == 10

function g(x: Int): Int { foo(mk(x)) + 1 }

method m(x: Int) {
    assert g(x) == 11
}
"#;
    let program = lower(input);
    let result = verify_named_method(&program, "m");
    assert!(
        result.is_ok(),
        "posts should propagate to the transitive call site; got {result:?}"
    );
}

#[test]
fn postcondition_wd_under_precondition() {
    // Post WD depends on pre truth: the divisor obligation inside
    // `safediv#ensures`'s body is only provable under the entry
    // `assume safediv#requires(x, y)` (mirroring the heap-dependent
    // `FromSnap` entry).
    let input = r#"
function safediv(x: Int, y: Int): Int
    requires y != 0
    ensures result == x / y
{ x / y }
"#;
    let program = lower(input);
    assert!(
        verify_named_function(&program, "safediv#ensures").is_ok(),
        "post WD must hold under the assumed precondition"
    );
    assert!(
        verify_named_function(&program, "safediv").is_ok(),
        "body + exit post check must verify"
    );
}

#[test]
fn recursive_function_postcondition_by_induction() {
    // Induction via the limited encoding: while checking `f`'s body, `f`'s own
    // spec-derived post rule is installed (Silicon's phase-1 `post` axiom), so
    // the recursive call's post (`f(next(x)) == 0`, guarded by
    // `ok(next(x))` from the axiom) discharges the exit assert. At the outer
    // call site the post rides the certificate's post fact.
    let input = r#"
domain D {
    function ok(x: Int): Bool
    function next(x: Int): Int
    axiom { forall x: Int :: {next(x)} ok(next(x)) }
}

function f(x: Int): Int
    requires ok(x)
    ensures result == 0
{ x == 0 ? 0 : f(next(x)) }

method m(x: Int)
    requires ok(x)
{
    assert f(x) == 0
}
"#;
    let program = lower(input);
    let analyzed = crate::vmir::analyze(program).expect("recursive function SCC accepted");
    let results = crate::verify::verify(&analyzed);
    for (name, r) in &results {
        assert!(r.is_ok(), "{name} should verify; got {r:?}");
    }
}

#[test]
fn failed_function_exports_no_facts() {
    // Success gating: `g` cannot prove `foo`'s precondition, so `g` itself
    // fails — and none of its axioms (definition, facts) may install. `m`
    // then knows nothing about `g` and fails too, instead of receiving facts
    // proven from a refuted premise.
    let input = r#"
domain D { function ok(y: Int): Bool }

function foo(y: Int): Int
    requires ok(y)
    ensures result == 10

function g(x: Int): Int { foo(x) + 1 }

method m(x: Int) {
    assert g(x) == 11
}
"#;
    let program = lower(input);
    let analyzed = crate::vmir::analyze(program).expect("acyclic");
    let results = crate::verify::verify(&analyzed);
    let get = |n: &str| {
        results
            .iter()
            .find(|(name, _)| name == n)
            .unwrap_or_else(|| panic!("no result for {n}"))
    };
    assert!(get("g").1.is_err(), "g cannot prove foo's precondition");
    assert!(
        get("m").1.is_err(),
        "a failed g must not export its definition or facts to m"
    );
}
