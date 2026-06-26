//! Tests for the Silver -> VMIR translation.

use super::*;
use crate::viper::{
    GlobalsCollector, IdentCollector, disambiguate, inline_macros, typecheck_program, viper_parser,
    walk::AstWalkable,
};

fn run(input: &str) -> vmir::Program {
    let mut program = viper_parser::vpr_program(input).expect("parse failed");
    let mut ident_collector = IdentCollector::default();
    program.walk_mut(&mut ident_collector);
    let interner = ident_collector.finalize();
    let mut globals_collector = GlobalsCollector::new(&interner);
    program.walk(&mut globals_collector);
    let globals = globals_collector.finalize().expect("globals error");
    disambiguate(&mut program, &interner, &globals).expect("disambiguation failed");
    inline_macros(&mut program, &interner).expect("macro inlining failed");
    let typed = typecheck_program(&mut program, &interner, &globals).expect("typecheck failed");
    translate(&typed, &interner, &globals).expect("translation failed")
}

#[test]
fn translates_number_pred_simpler() {
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
    let p = run(input);

    // No `@snap`/`@addr` decls are emitted; the snapshot type and address
    // location are derived from the predicate's own id.
    assert!(p.interner.get("number@snap").is_none());
    assert!(p.interner.get("number@addr").is_none());

    let pred_id = p.interner.get("number").expect("missing number");

    // Predicate itself is abstract; its address location is derived.
    let vmir::Declaration::Resource(pred) = &p.decls[pred_id] else {
        panic!("number must be a Resource");
    };
    assert!(
        pred.body.is_none(),
        "abstract predicate must have body=None"
    );
    let group = p.groups.get("number").expect("predicate group tag");
    let addr_fn = pred.derive_location(pred_id, group);
    assert_eq!(addr_fn.params, vec![vmir::Type::Ref]);
    assert_eq!(
        addr_fn.ret,
        vmir::Type::addr(group, vmir::Type::Snap(pred_id), vmir::Bound::Unbounded)
    );
    // Abstract predicate (no body) derives an opaque empty Domain snapshot.
    assert!(matches!(
        pred.derive_snapshot(),
        Some(vmir::Snapshot::Abstract(_))
    ));

    // Method contracts.
    for name in [
        "assign#ensures",
        "read#requires",
        "read#ensures",
        "add#requires",
        "add#ensures",
    ] {
        let id = p
            .interner
            .get(name)
            .unwrap_or_else(|| panic!("missing resource {name}"));
        assert!(
            matches!(&p.decls[id], vmir::Declaration::Resource(r) if r.body.is_some()),
            "{name} must be a concrete Resource"
        );
    }
    assert!(
        p.interner.get("assign#requires").is_none(),
        "assign has no precondition; #requires must not exist"
    );

    // The read#requires body must reference the predicate's address
    // location (`Location(number_id, ..)` — the predicate's own id) and an
    // Acc on its result, NOT a ResourceCall on number.
    let read_req_id = p.interner.get("read#requires").unwrap();
    let vmir::Declaration::Resource(read_req) = &p.decls[read_req_id] else {
        unreachable!();
    };
    let body = read_req.body.as_ref().unwrap();
    let mut saw_addr_call = false;
    let mut saw_acc = false;
    let number_group = p.groups.get("number").expect("number group tag");
    for inst in &body.insts {
        match &inst.kind {
            // An address is an ordinary call to the predicate's address
            // function (its own id), result type grouped under `number`.
            vmir::InstKind::Pure(
                vmir::Type::Addr { group, .. },
                vmir::PureInst::FunctionCall(None, fc),
            ) if *group == number_group && fc.function == pred_id => {
                saw_addr_call = true;
            }
            vmir::InstKind::Heap(vmir::HeapInst::Combine { .. }) => saw_acc = true,
            _ => {}
        }
    }
    assert!(saw_addr_call, "read#requires must address number");
    assert!(saw_acc, "read#requires must contain an acc");

    // The `add` body's method contracts lower to resource inhale/exhale
    // instructions: an `exhale` of `add#requires` (implicit assert) and an
    // `inhale` of `add#ensures` (implicit assume). No standalone
    // Assert/Assume/ResourceCall remain.
    let add_id = p.interner.get("add").expect("missing add method");
    let vmir::Declaration::Method(add) = &p.decls[add_id] else {
        panic!("add must be a Method");
    };
    let kinds: Vec<_> = add.insts.iter().map(|i| &i.kind).collect();
    assert!(
        kinds
            .iter()
            .any(|k| matches!(k, vmir::InstKind::Heap(vmir::HeapInst::Exhale { .. }))),
        "add body must contain an exhale (requires)"
    );
    assert!(
        kinds
            .iter()
            .any(|k| matches!(k, vmir::InstKind::Heap(vmir::HeapInst::Inhale { .. }))),
        "add body must contain an inhale (ensures)"
    );
    assert!(
        !kinds
            .iter()
            .any(|k| matches!(k, vmir::InstKind::Assert(_) | vmir::InstKind::Assume(_))),
        "resource bools are now implicit in the combine; no standalone Assert/Assume"
    );

    // Display smoke: must not panic.
    let _ = format!("{p}");
}

#[test]
fn div_inside_ternary_branch_carries_guard() {
    // The division only executes on the path where the guard holds, so the
    // emitted `Div` instruction must carry a non-empty path condition.
    let input = r#"
method m(x: Int, y: Int)
    requires y != 0 ? x / y == x : true
"#;
    let p = run(input);

    let req_id = p.interner.get("m#requires").expect("missing m#requires");
    let vmir::Declaration::Resource(req) = &p.decls[req_id] else {
        panic!("m#requires must be a Resource");
    };
    let body = req.body.as_ref().unwrap();

    let div = body
        .insts
        .iter()
        .find(|i| {
            matches!(
                &i.kind,
                vmir::InstKind::Pure(_, vmir::PureInst::Binary(vmir::BinOp::Div, _, _))
            )
        })
        .expect("requires body must contain a Div");
    assert!(
        !div.pc.conds.is_empty(),
        "Div inside the ternary then-branch must be guarded by a path condition"
    );
}

#[test]
fn if_else_arms_carry_complementary_path_conditions() {
    // Each arm's guarded instructions (the `assert`s) must run under the
    // branch condition: `<c>` in the then-arm, `<!c>` in the else-arm.
    let input = r#"
method m(c: Bool, x: Int)
{
    if (c) { assert x == x } else { assert x == x }
}
"#;
    let p = run(input);
    let m_id = p.interner.get("m").expect("missing m");
    let vmir::Declaration::Method(m) = &p.decls[m_id] else {
        panic!("m must be a Method");
    };
    // params: c = Temp(0), x = Temp(1); the branch cond is the bare param c.
    let c = vmir::Val::Temp(0);
    let asserts: Vec<&vmir::PathConds> = m
        .insts
        .iter()
        .filter_map(|i| matches!(i.kind, vmir::InstKind::Assert(_)).then_some(&i.pc))
        .collect();
    assert_eq!(asserts.len(), 2, "one assert per arm");
    assert!(
        asserts
            .iter()
            .any(|pc| pc.conds == vec![(c.clone(), vmir::Polarity::Positive)]),
        "then-arm assert must be guarded by <c>"
    );
    assert!(
        asserts
            .iter()
            .any(|pc| pc.conds == vec![(c.clone(), vmir::Polarity::Negative)]),
        "else-arm assert must be guarded by <!c>"
    );
}

#[test]
fn structured_nesting_keeps_pcs_minimal() {
    // Structured (reducible) nesting must never produce a pc fatter than the
    // enclosing split: inside `if a { if b { .. } }` the guard is exactly the
    // two real branch literals `<a, b>` (no materialized OR), and each merge
    // returns to the dominator's pc — the final `ensures` exhale carries `<>`.
    let input = r#"
field f: Int

method m(a: Bool, b: Bool, x: Ref)
    requires acc(x.f, 1/1)
    ensures acc(x.f, 1/1)
{
    if (a) {
        if (b) {
            assert true
        }
    }
}
"#;
    let p = run(input);
    let m_id = p.interner.get("m").expect("missing m");
    let vmir::Declaration::Method(m) = &p.decls[m_id] else {
        panic!("m must be a Method");
    };
    // params: a = Temp(0), b = Temp(1).
    let assert = m
        .insts
        .iter()
        .find(|i| matches!(i.kind, vmir::InstKind::Assert(_)))
        .expect("inner assert");
    assert_eq!(
        assert.pc.conds,
        vec![
            (vmir::Val::Temp(0), vmir::Polarity::Positive),
            (vmir::Val::Temp(1), vmir::Polarity::Positive),
        ],
        "nested guard must be the two real branch literals <a, b>, not a materialized OR"
    );
    let exhale = m
        .insts
        .iter()
        .find(|i| matches!(&i.kind, vmir::InstKind::Heap(vmir::HeapInst::Exhale { .. })))
        .expect("ensures exhale");
    assert!(
        exhale.pc.conds.is_empty(),
        "both merges return to the dominator pc; final exhale is <>, got {:?}",
        exhale.pc
    );
}

#[test]
fn exhaustive_three_way_join_minimizes_to_empty_pc() {
    // A 3-way `goto` join whose reach is `a ∨ (!a∧b) ∨ (!a∧!b)` — a tautology.
    // Cube minimization (`merge_cubes`) collapses it, so the post-merge
    // `ensures` exhale must carry the trivial `<>`, not a materialized-OR
    // literal: the permission stays ungated.
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
    let p = run(input);
    let m_id = p.interner.get("m").expect("missing m");
    let vmir::Declaration::Method(m) = &p.decls[m_id] else {
        panic!("m must be a Method");
    };
    let exhale = m
        .insts
        .iter()
        .find(|i| matches!(&i.kind, vmir::InstKind::Heap(vmir::HeapInst::Exhale { .. })))
        .expect("ensures lowers to an exhale");
    assert!(
        exhale.pc.conds.is_empty(),
        "exhaustive 3-way join must minimize to <>, got {:?}",
        exhale.pc
    );
}

#[test]
fn join_inserts_phi_for_divergent_variable() {
    // `r` takes different values on the two arms, so the merge block must
    // reconcile it with a phi `c ? a : b`; the merged value flows into the
    // postcondition with the trivial `<>` path condition.
    let input = r#"
method m(c: Bool, a: Int, b: Int) returns (r: Int)
{
    if (c) { r := a } else { r := b }
}
"#;
    let p = run(input);
    let m_id = p.interner.get("m").expect("missing m");
    let vmir::Declaration::Method(m) = &p.decls[m_id] else {
        panic!("m must be a Method");
    };
    // params: c=Temp(0), a=Temp(1), b=Temp(2); ret r=Temp(3).
    let phi = m
        .insts
        .iter()
        .find(|i| {
            matches!(
                &i.kind,
                vmir::InstKind::Pure(_, vmir::PureInst::Ternary(c, t, e))
                    if *c == vmir::Val::Temp(0)
                        && *t == vmir::Val::Temp(1)
                        && *e == vmir::Val::Temp(2)
            )
        })
        .expect("merge must emit phi `c ? a : b`");
    assert!(phi.pc.conds.is_empty(), "phi itself is unguarded");
}

#[test]
fn lowers_generic_adt_type_parameters() {
    // A generic ADT's declared field types keep their type parameters
    // (`Generic(i)`) and nested ADT structure; a use at a concrete
    // instantiation lowers to `Domain(head, [concrete args])` — never the
    // erased `Ref` placeholder, so the monomorphization key is faithful.
    let input = r#"
adt List[T] {
    Nil()
    Cons(head: T, tail: List[T])
}

function len(l: List[Int]): Int
"#;
    let p = run(input);
    let list_id = p.interner.get("List").expect("missing List");

    let vmir::Declaration::Adt(adt) = &p.decls[list_id] else {
        panic!("List must be an Adt");
    };
    // Variant 0 = `Nil()` (no fields); variant 1 = `Cons(?0, List[?0])`.
    assert!(adt.variants[0].field_types.is_empty(), "Nil has no fields");
    assert_eq!(
        adt.variants[1].field_types,
        vec![
            vmir::Type::Generic(0),
            vmir::Type::Domain(list_id, Box::new([vmir::Type::Generic(0)])),
        ],
        "Cons field types must be [?0, List[?0]], not erased to Ref"
    );

    // `len`'s parameter is `List[Int]` — a concrete monomorphization.
    let len_id = p.interner.get("len").expect("missing len");
    let vmir::Declaration::Function(func) = &p.decls[len_id] else {
        panic!("len must be a Function");
    };
    assert_eq!(
        func.params,
        vec![vmir::Type::Domain(list_id, Box::new([vmir::Type::Int]))],
        "len's param must lower to List[Int], not Ref"
    );
}
