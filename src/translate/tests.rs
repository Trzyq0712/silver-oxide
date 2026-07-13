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
    let typed = typecheck_program(&mut program, interner, &globals).expect("typecheck failed");
    translate(&typed).expect("translation failed")
}

/// Run the pipeline through translation, expecting it to fail, and return the
/// first `TranslationError`.
fn run_err(input: &str) -> TranslationError {
    let mut program = viper_parser::vpr_program(input).expect("parse failed");
    let mut ident_collector = IdentCollector::default();
    program.walk_mut(&mut ident_collector);
    let interner = ident_collector.finalize();
    let mut globals_collector = GlobalsCollector::new(&interner);
    program.walk(&mut globals_collector);
    let globals = globals_collector.finalize().expect("globals error");
    disambiguate(&mut program, &interner, &globals).expect("disambiguation failed");
    inline_macros(&mut program, &interner).expect("macro inlining failed");
    let typed = typecheck_program(&mut program, interner, &globals).expect("typecheck failed");
    translate(&typed)
        .expect_err("expected translation to fail")
        .into_iter()
        .next()
        .expect("expected at least one error")
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
    assert!(p.id("number@snap").is_none());
    assert!(p.id("number@addr").is_none());

    let pred_id = p.id("number").expect("missing number");

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
    assert_eq!(addr_fn.params, vec![vmir::Type::Ref].into());
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
            .id(name)
            .unwrap_or_else(|| panic!("missing resource {name}"));
        assert!(
            matches!(&p.decls[id], vmir::Declaration::Resource(r) if r.body.is_some()),
            "{name} must be a concrete Resource"
        );
    }
    assert!(
        p.id("assign#requires").is_none(),
        "assign has no precondition; #requires must not exist"
    );

    // The read#requires body must reference the predicate's address
    // location (`Location(number_id, ..)` — the predicate's own id) and an
    // Acc on its result, NOT a ResourceCall on number.
    let read_req_id = p.id("read#requires").unwrap();
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
                vmir::PureInst::FunctionCall(fc),
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
    let add_id = p.id("add").expect("missing add method");
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

    let req_id = p.id("m#requires").expect("missing m#requires");
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
fn int_div_lowers_to_a_guarded_div() {
    // `\` is Silver's integer division (`/` is permission division). It carries
    // the same divisor≠0 obligation and collapses into the polymorphic VMIR
    // `Div`, whose operands are `Int` here.
    let input = r#"
method m(x: Int, y: Int)
    requires y != 0 ==> x \ y == x
"#;
    let p = run(input);

    let req_id = p.id("m#requires").expect("missing m#requires");
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
                vmir::InstKind::Pure(
                    vmir::Type::Int,
                    vmir::PureInst::Binary(vmir::BinOp::Div, _, _)
                )
            )
        })
        .expect("requires body must contain an Int-typed Div");
    assert!(
        !div.pc.conds.is_empty(),
        "the divisor≠0 obligation is discharged under the implication's guard"
    );
    assert!(
        div.heap.is_some(),
        "a Div is an obligation, so it checks in against the current heap"
    );
}

#[test]
fn int_div_on_perm_operands_is_a_type_error() {
    // Unlike `/`, `\` is strictly Int × Int → Int, so it never reaches translation.
    let input = r#"
method m(x: Perm, y: Perm)
    requires x \ y == x
"#;
    let mut program = viper_parser::vpr_program(input).expect("parse failed");
    let mut ident_collector = IdentCollector::default();
    program.walk_mut(&mut ident_collector);
    let interner = ident_collector.finalize();
    let mut globals_collector = GlobalsCollector::new(&interner);
    program.walk(&mut globals_collector);
    let globals = globals_collector.finalize().expect("globals error");
    disambiguate(&mut program, &interner, &globals).expect("disambiguation failed");
    inline_macros(&mut program, &interner).expect("macro inlining failed");
    typecheck_program(&mut program, interner, &globals)
        .expect_err("`\\` on Perm operands must be rejected");
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
    let m_id = p.id("m").expect("missing m");
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
    let m_id = p.id("m").expect("missing m");
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
    let m_id = p.id("m").expect("missing m");
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
    let m_id = p.id("m").expect("missing m");
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
    let list_id = p.id("List").expect("missing List");

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
    let len_id = p.id("len").expect("missing len");
    let vmir::Declaration::Function(func) = &p.decls[len_id] else {
        panic!("len must be a Function");
    };
    assert_eq!(
        func.params,
        Into::<vmir::Params>::into(vec![vmir::Type::Domain(
            list_id,
            Box::new([vmir::Type::Int])
        )]),
        "len's param must lower to List[Int], not Ref"
    );
}

#[test]
fn generic_domain_rejected() {
    // Generics live on ADTs. A generic domain's axioms could only be
    // instantiated off a *type* trigger, which Silver has no syntax to write —
    // rather than infer one, translation refuses the domain.
    let err = run_err(
        r#"
domain Box[T] {
    function wrap(x: T): T
}
"#,
    );
    assert_eq!(
        err,
        TranslationError::GenericDomainUnsupported("Box".to_string())
    );
}

/// A heapless obligation (`assert`, division) carries the current check-in heap
/// on its `Inst`; `assume` (no verification) and a heap-embedding `Deref` do not.
#[test]
fn obligations_carry_check_in_heap() {
    use vmir::{BinOp, InstKind, PureInst};
    let input = r#"
field f: Int

method m(x: Ref, y: Int)
    requires acc(x.f, write)
{
    var z: Int := x.f / y
    assert z == z
    assume y > 0
}
"#;
    let p = run(input);
    let m_id = p.id("m").expect("missing m");
    let vmir::Declaration::Method(method) = &p.decls[m_id] else {
        panic!("m must be a Method");
    };

    let mut saw_div = false;
    let mut saw_assert = false;
    let mut saw_assume = false;
    let mut saw_deref = false;
    for inst in &method.insts {
        match &inst.kind {
            InstKind::Pure(_, PureInst::Binary(BinOp::Div, _, _)) => {
                saw_div = true;
                assert!(inst.heap.is_some(), "division must carry a check-in heap");
            }
            InstKind::Pure(_, PureInst::Deref(..)) => {
                saw_deref = true;
                assert!(
                    inst.heap.is_none(),
                    "deref embeds its heap; no check-in heap"
                );
            }
            InstKind::Assert(_) => {
                saw_assert = true;
                assert!(inst.heap.is_some(), "assert must carry a check-in heap");
            }
            InstKind::Assume(_) => {
                saw_assume = true;
                assert!(inst.heap.is_none(), "assume does no verification; no heap");
            }
            _ => {}
        }
    }
    assert!(saw_div, "expected a division inst");
    assert!(saw_assert, "expected an assert inst");
    assert!(saw_assume, "expected an assume inst");
    assert!(saw_deref, "expected a deref inst");
}

#[test]
fn function_lowers_requires_ensures_and_body() {
    // Heap-free function: `#requires` / `#ensures` are boolean Functions; the
    // body assumes the precondition at entry. Postcondition stitching is
    // disabled for now — `#ensures` is still declared but never asserted.
    let input = r#"
function get(x: Int): Int
    requires x > 0
    ensures result == x
{
    x
}
"#;
    let p = run(input);

    // #requires is a boolean Function `params -> Bool` (NOT a Resource).
    let req_id = p.id("get#requires").expect("missing get#requires");
    let vmir::Declaration::Function(req) = &p.decls[req_id] else {
        panic!("get#requires must be a Function");
    };
    assert_eq!(req.ret, vmir::Type::Bool);
    assert_eq!(req.params, vec![vmir::Type::Int].into());
    assert!(req.body.is_some());

    // #ensures is a boolean Function over (params ++ result).
    let ens_id = p.id("get#ensures").expect("missing get#ensures");
    let vmir::Declaration::Function(ens) = &p.decls[ens_id] else {
        panic!("get#ensures must be a Function");
    };
    assert_eq!(ens.ret, vmir::Type::Bool);
    assert_eq!(
        ens.params,
        vec![vmir::Type::Int, vmir::Type::Int].into(),
        "ensures params are the function params ++ result"
    );
    assert!(ens.body.is_some());

    // The main function's body: assume #requires at entry, assert #ensures at exit.
    let get_id = p.id("get").expect("missing get");
    let vmir::Declaration::Function(get) = &p.decls[get_id] else {
        panic!("get must be a Function");
    };
    assert_eq!(get.ret, vmir::Type::Int);
    let body = get.body.as_ref().expect("function body must be lowered");
    let is_call = |i: usize, f: vmir::MemberId| {
        matches!(
            &body.insts[i].kind,
            vmir::InstKind::Pure(vmir::Type::Bool, vmir::PureInst::FunctionCall(fc))
                if fc.function == f
        )
    };
    assert!(is_call(0, req_id), "entry must call get#requires");
    assert!(
        matches!(&body.insts[1].kind, vmir::InstKind::Assume(_)),
        "entry must assume the precondition"
    );
    // Exit stitching: the body ends with a call to `get#ensures` followed by
    // the exit assert (the definition-side postcondition check).
    let n = body.insts.len();
    assert!(
        is_call(n - 2, ens_id),
        "exit must call get#ensures(params, result)"
    );
    assert!(
        matches!(&body.insts[n - 1].kind, vmir::InstKind::Assert(_)),
        "exit must assert the postcondition"
    );
    // Contract links on the main decl: requires over the params, ensures over
    // params ++ result.
    let Some(vmir::Requires::Pure(rq)) = get.requires.as_ref() else {
        panic!("heap-free function links a boolean requires function");
    };
    assert_eq!(rq.member, req_id);
    assert_eq!(rq.args, vec![vmir::Val::Temp(0)]);
    let en = get.ensures.as_ref().expect("ensures link");
    assert_eq!(en.member, ens_id);
    assert_eq!(
        en.args,
        vec![
            vmir::ContractArg::Val(vmir::Val::Temp(0)),
            vmir::ContractArg::Result
        ]
    );
    // The `#ensures` decl itself links back to `#requires` (its body's facts
    // are proven under the entry pre assumption).
    let vmir::Declaration::Function(ens) = &p.decls[ens_id] else {
        unreachable!()
    };
    assert_eq!(ens.requires.as_ref().map(|r| r.member()), Some(req_id));
    assert!(
        ens.body
            .as_ref()
            .is_some_and(|b| matches!(b.insts[1].kind, vmir::InstKind::Assume(_))),
        "ensures body must open with `assume get#requires(params)` (post WD under pre)"
    );
}

#[test]
fn precondition_free_function_has_no_requires() {
    let input = r#"
function inc(x: Int): Int
    ensures result == x + 1
{
    x + 1
}
"#;
    let p = run(input);

    assert!(
        p.id("inc#requires").is_none(),
        "no requires => no contract fn"
    );

    let ens_id = p.id("inc#ensures").expect("missing inc#ensures");
    let vmir::Declaration::Function(ens) = &p.decls[ens_id] else {
        panic!("inc#ensures must be a Function");
    };
    assert_eq!(ens.ret, vmir::Type::Bool);

    let inc_id = p.id("inc").expect("missing inc");
    let vmir::Declaration::Function(inc) = &p.decls[inc_id] else {
        panic!("inc must be a Function");
    };
    // No precondition ⟹ no entry assume and no requires link. The exit still
    // calls and asserts `inc#ensures(params, result)`.
    let body = inc.body.as_ref().expect("body");
    assert!(
        !body
            .insts
            .iter()
            .any(|i| matches!(i.kind, vmir::InstKind::Assume(_))),
        "no requires ⟹ no entry assume"
    );
    assert!(inc.requires.is_none(), "no requires ⟹ no requires link");
    let n = body.insts.len();
    assert!(
        matches!(
            &body.insts[n - 2].kind,
            vmir::InstKind::Pure(_, vmir::PureInst::FunctionCall(fc)) if fc.function == ens_id
        ),
        "exit must call inc#ensures(params, result)"
    );
    assert!(
        matches!(&body.insts[n - 1].kind, vmir::InstKind::Assert(_)),
        "exit must assert the postcondition"
    );
    assert_eq!(inc.ensures.as_ref().map(|e| e.member), Some(ens_id));
}

#[test]
fn heap_dependent_function_lowers_to_snapshot_passing() {
    // A function whose precondition grants permission (`acc`) is heap-dependent:
    // - `get#requires` is a self-framed Resource (footprint + bool);
    // - `get` gains a trailing snapshot parameter `Snap(get#requires)`; its body
    //   opens with `FromSnap` (no boolean entry assume — the resource bool is
    //   assumed implicitly) and closes with `assert get#ensures(x, result, s)`;
    // - `get#ensures` is a boolean Function over (params ++ [result, snap]) whose
    //   body also opens with `FromSnap`, so it can read the precondition heap.
    let input = r#"
field f: Int
function get(x: Ref): Int
    requires acc(x.f) && x.f > 0
    ensures result == x.f
{ x.f }
"#;
    let p = run(input);

    // #requires is a self-framed Resource, not a boolean Function.
    let req_id = p.id("get#requires").expect("missing get#requires");
    let vmir::Declaration::Resource(req) = &p.decls[req_id] else {
        panic!("get#requires must be a Resource");
    };
    assert_eq!(req.params, vec![vmir::Type::Ref]);
    assert!(matches!(req.precond, vmir::Precond::SelfFramed));
    assert!(req.body.is_some());

    let snap_ty = vmir::Type::Snap(req_id);

    // Main function: params ++ [Snap(get#requires)] -> Int.
    let get_id = p.id("get").expect("missing get");
    let vmir::Declaration::Function(get) = &p.decls[get_id] else {
        panic!("get must be a Function");
    };
    assert_eq!(get.ret, vmir::Type::Int);
    assert_eq!(
        get.params,
        vec![vmir::Type::Ref, snap_ty.clone()].into(),
        "heap-dep function takes its precondition snapshot as trailing param"
    );
    let body = get.body.as_ref().expect("body must be lowered");
    // Entry: FromSnap reconstructing the precondition heap from the snap param.
    assert!(
        matches!(
            &body.insts[0].kind,
            vmir::InstKind::Heap(vmir::HeapInst::FromSnap { resource, args, snap })
                if *resource == req_id
                    && args == &vec![vmir::Val::Temp(0)]
                    && *snap == vmir::Val::Temp(1)
        ),
        "body must open with FromSnap of get#requires"
    );
    // No boolean entry assume — FromSnap assumes the resource bool implicitly.
    assert!(
        !body
            .insts
            .iter()
            .any(|i| matches!(i.kind, vmir::InstKind::Assume(_))),
        "heap-dep body has no boolean entry assume"
    );
    // Exit: `assert get#ensures(params, result, s)` — the snapshot rides along,
    // so the postcondition can read the precondition heap.
    let ens_id = p.id("get#ensures").expect("missing get#ensures");
    let n = body.insts.len();
    assert!(
        matches!(
            &body.insts[n - 2].kind,
            vmir::InstKind::Pure(_, vmir::PureInst::FunctionCall(fc))
                if fc.function == ens_id
                    && fc.args.iter().cloned().collect::<Vec<_>>()
                        == vec![vmir::Val::Temp(0), body.res.clone(), vmir::Val::Temp(1)]
        ),
        "exit must call get#ensures(params, result, snap)"
    );
    assert!(
        matches!(&body.insts[n - 1].kind, vmir::InstKind::Assert(_)),
        "exit must assert the postcondition"
    );

    // #ensures: boolean Function over (params ++ [result, snap]), body opens
    // with the same FromSnap.
    let vmir::Declaration::Function(ens) = &p.decls[ens_id] else {
        panic!("get#ensures must be a Function");
    };
    assert_eq!(ens.ret, vmir::Type::Bool);
    assert_eq!(
        ens.params,
        vec![vmir::Type::Ref, vmir::Type::Int, snap_ty].into(),
        "ensures params are params ++ [result, snap]"
    );
    let ens_body = ens.body.as_ref().expect("ensures body");
    assert!(
        matches!(
            &ens_body.insts[0].kind,
            vmir::InstKind::Heap(vmir::HeapInst::FromSnap { resource, snap, .. })
                if *resource == req_id && *snap == vmir::Val::Temp(2)
        ),
        "ensures body must open with FromSnap (snap after result)"
    );
}

#[test]
fn heap_dependent_function_call_passes_snapshot() {
    // A call to a heap-dependent function narrows the caller's heap with `Snap`
    // (implicit precondition check), passes the snapshot as the extra trailing
    // argument, and assumes `f#ensures(args, ret, snap)` — no boolean
    // requires-assert.
    let input = r#"
field f: Int
function get(x: Ref): Int
    requires acc(x.f)
{ x.f }

method m(y: Ref)
    requires acc(y.f)
{
    var a: Int := get(y)
}
"#;
    let p = run(input);
    let req_id = p.id("get#requires").expect("missing get#requires");
    let get_id = p.id("get").expect("missing get");
    let m_id = p.id("m").expect("missing method m");
    let vmir::Declaration::Method(m) = &p.decls[m_id] else {
        panic!("m must be a Method");
    };
    let snap_at = m.insts.iter().position(|i| {
        matches!(
            &i.kind,
            vmir::InstKind::Pure(vmir::Type::Snap(r), vmir::PureInst::Snap { resource, .. })
                if *r == req_id && *resource == req_id
        )
    });
    let snap_at = snap_at.expect("call site must emit a Snap of get#requires");
    // The following FunctionCall must carry the snapshot as its last argument.
    let call = m.insts[snap_at..].iter().find_map(|i| match &i.kind {
        vmir::InstKind::Pure(_, vmir::PureInst::FunctionCall(fc)) if fc.function == get_id => {
            Some(fc)
        }
        _ => None,
    });
    let call = call.expect("call to get after the Snap");
    let args: Vec<_> = call.args.iter().cloned().collect();
    assert_eq!(args.len(), 2, "call args are (y, snap)");
    // No boolean requires-assert for a heap-dep callee (Snap checks implicitly);
    // `m` has no other assert-producing constructs before the call.
    assert!(
        !m.insts[..snap_at]
            .iter()
            .any(|i| matches!(i.kind, vmir::InstKind::Assert(_))),
        "no boolean requires-assert before a heap-dep call"
    );
}

#[test]
fn function_call_emits_use_side_contract() {
    // A method calling a function with contracts must, at the call site,
    // assert `f#requires(args)` before the call. A call to a contract-free
    // function doesn't. Postcondition stitching is disabled for now: the
    // callee's `f#ensures` is never called or assumed at the use site.
    let input = r#"
function inc(x: Int): Int
    requires x > 0
    ensures result == x + 1
{
    x + 1
}

function raw(x: Int): Int
{
    x + 1
}

method m() {
    var a: Int := inc(3)
    var b: Int := raw(4)
}
"#;
    let p = run(input);
    let inc_req = p.id("inc#requires").expect("missing inc#requires");
    let inc_ens = p.id("inc#ensures").expect("missing inc#ensures");
    assert!(p.id("raw#requires").is_none() && p.id("raw#ensures").is_none());

    let m_id = p.id("m").expect("missing m");
    let vmir::Declaration::Method(m) = &p.decls[m_id] else {
        panic!("m must be a Method");
    };
    let calls = |f: vmir::MemberId| {
        m.insts.iter().position(|i| {
            matches!(
                &i.kind,
                vmir::InstKind::Pure(_, vmir::PureInst::FunctionCall(fc)) if fc.function == f
            )
        })
    };

    // `inc#requires(..)` call is followed by an assert.
    let req_pos = calls(inc_req).expect("inc#requires call");
    assert!(matches!(
        &m.insts[req_pos + 1].kind,
        vmir::InstKind::Assert(_)
    ));
    // `inc#ensures` is declared but never called from `m`'s body — postcondition
    // stitching is disabled.
    assert!(calls(inc_ens).is_none(), "inc#ensures is never called");
    // requires-assert precedes the `inc` value call.
    let inc_pos = calls(p.id("inc").unwrap()).expect("inc call");
    assert!(req_pos < inc_pos);

    // Exactly one assert (the requires check), no assume (raw contributes
    // neither, and postconditions aren't assumed).
    let count =
        |pred: fn(&vmir::InstKind) -> bool| m.insts.iter().filter(|i| pred(&i.kind)).count();
    assert_eq!(count(|k| matches!(k, vmir::InstKind::Assert(_))), 1);
    assert_eq!(count(|k| matches!(k, vmir::InstKind::Assume(_))), 0);
}

#[test]
fn translation_error_returns_err_without_panicking() {
    // A predicate body using a `wildcard` permission is valid Silver (parses
    // and typechecks) but not yet lowerable —
    // `TranslationError::Unsupported("wildcard literal")` in `pure_exp.rs`'s
    // `lower_literal`. `PredicateTranslator::define` bails with `?`, leaving its
    // `DeclSlot<vmir::Resource>` unfilled; the slot is simply dropped and the
    // whole `Builder` discarded as the error propagates — no panic, no cleanup.
    let input = r#"
field f: Int

predicate broken(this: Ref) {
    acc(this.f, wildcard)
}
"#;
    let mut program = viper_parser::vpr_program(input).expect("parse failed");
    let mut ident_collector = IdentCollector::default();
    program.walk_mut(&mut ident_collector);
    let interner = ident_collector.finalize();
    let mut globals_collector = GlobalsCollector::new(&interner);
    program.walk(&mut globals_collector);
    let globals = globals_collector.finalize().expect("globals error");
    disambiguate(&mut program, &interner, &globals).expect("disambiguation failed");
    inline_macros(&mut program, &interner).expect("macro inlining failed");
    let typed = typecheck_program(&mut program, interner, &globals).expect("typecheck failed");

    // Must return `Err` cleanly — no panic from the unfilled `DeclSlot`.
    match translate(&typed) {
        Err(errors) => assert!(!errors.is_empty(), "expected at least one error"),
        Ok(_) => panic!("expected translation to reject the wildcard permission"),
    }
}

#[test]
fn function_display_smoke() {
    let input = r#"
function get(x: Int): Int
    requires x > 0
    ensures result == x
{
    x
}
"#;
    let p = run(input);
    // Exercise the Display path (must not panic) and sanity-check the rendering.
    let s = format!("{p}");
    assert!(s.contains("function get"), "rendered:\n{s}");
    assert!(s.contains("function get#ensures"), "rendered:\n{s}");
    assert!(s.contains("-> Bool"), "rendered:\n{s}");
    assert!(s.contains("result:"), "rendered:\n{s}");
}

#[test]
fn ground_axiom_lowers_to_domain_axiom() {
    let input = r#"
function one(): Int ensures result == 1 { 1 }
domain D {
    function size(): Int
    axiom sz { size() == 0 }
    axiom { one() == 1 }
}
"#;
    let p = run(input);

    // Named axiom: registered under its own name, monomorphic.
    let sz_id = p.id("sz").expect("missing axiom sz");
    let vmir::Declaration::Axiom(sz) = &p.decls[sz_id] else {
        panic!("sz must be a Axiom");
    };
    let size_id = p.id("size").expect("missing size");
    assert!(
        sz.body.insts.iter().any(|i| matches!(
            &i.kind,
            vmir::InstKind::Pure(_, vmir::PureInst::FunctionCall(fc)) if fc.function == size_id
        )),
        "axiom body must call size()"
    );

    // Anonymous axiom: generated slot name, and it calls `one()` (a normal,
    // precondition-free function). Postcondition stitching is disabled for
    // now, so the callee's `#ensures` is not assumed here.
    let anon_id = p.id("D#axiom1").expect("missing anonymous axiom slot");
    let vmir::Declaration::Axiom(anon) = &p.decls[anon_id] else {
        panic!("D#axiom1 must be a Axiom");
    };
    let one_id = p.id("one").expect("missing one");
    assert!(
        anon.body.insts.iter().any(|i| matches!(
            &i.kind,
            vmir::InstKind::Pure(_, vmir::PureInst::FunctionCall(fc)) if fc.function == one_id
        )),
        "axiom body must call one()"
    );
}

/// The single trigger group of a quantifier that has exactly one.
fn only_group(q: &vmir::Quantifier) -> &vmir::QuantTrigger {
    let [group] = &q.triggers[..] else {
        panic!("expected exactly one trigger group");
    };
    group
}

/// The single term of a trigger group that has exactly one, as an application:
/// `(head, args)`.
fn only_app(group: &vmir::QuantTrigger) -> (&vmir::TrigHead, &[vmir::TrigTerm]) {
    let [term] = &group.terms[..] else {
        panic!("expected exactly one trigger term");
    };
    let vmir::TrigTerm::App { head, args, .. } = term else {
        panic!("expected an application trigger term");
    };
    (head, args)
}

#[test]
fn forall_axiom_lowers_to_quantifier() {
    // A `forall` axiom lowers to a `Declaration::Quantifier` (occurrence body +
    // trigger) plus a ground axiom whose body is the nullary occurrence call.
    let input = r#"
domain D {
    function foo(i: Int): Bool
    axiom basic { forall i: Int :: {foo(i)} foo(i) }
}
"#;
    let p = run(input);
    let q_id = p.id("basic#quant0").expect("missing quantifier slot");
    let vmir::Declaration::Quantifier(q) = &p.decls[q_id] else {
        panic!("basic#quant0 must be a Quantifier");
    };
    assert_eq!(q.bound.len(), 1, "one binder");
    assert!(q.params.is_empty(), "top-level forall captures nothing");
    let foo_id = p.id("foo").expect("missing foo");
    let (head, args) = only_app(only_group(q));
    assert_eq!(*head, vmir::TrigHead::Func(foo_id), "trigger is foo");
    assert_eq!(args, &[vmir::TrigTerm::Bound(0)], "arg 0 binds bound var 0");

    // The axiom body references the occurrence via a nullary call to `q_id`.
    let ax_id = p.id("basic").expect("missing axiom basic");
    let vmir::Declaration::Axiom(ax) = &p.decls[ax_id] else {
        panic!("basic must be a Axiom");
    };
    assert!(
        ax.body.insts.iter().any(|i| matches!(
            &i.kind,
            vmir::InstKind::Pure(_, vmir::PureInst::FunctionCall(fc))
                if fc.function == q_id && fc.args.iter().next().is_none()
        )),
        "axiom body must call the nullary occurrence"
    );

    // Display path must not panic and should name the quantifier.
    let s = format!("{p}");
    assert!(s.contains("quantifier basic#quant0"), "rendered:\n{s}");
}

#[test]
fn forall_in_method_inhale_lowers_to_quantifier() {
    // A `forall` in a method-body `inhale` lowers to a `{method}#quant{j}`
    // declaration; the free method param becomes a capture, passed as the
    // occurrence call's argument in the method body.
    let input = r#"
domain D { function g(a: Int, i: Int): Bool }
method m(x: Int) {
    inhale forall i: Int :: {g(x, i)} g(x, i)
}
"#;
    let p = run(input);
    let q_id = p.id("m#quant0").expect("missing quantifier slot");
    let vmir::Declaration::Quantifier(q) = &p.decls[q_id] else {
        panic!("m#quant0 must be a Quantifier");
    };
    assert_eq!(q.params.len(), 1, "captures the method param x");
    assert_eq!(q.bound.len(), 1, "one binder");
    let g_id = p.id("g").expect("missing g");
    let (head, args) = only_app(only_group(q));
    assert_eq!(*head, vmir::TrigHead::Func(g_id));
    assert_eq!(
        args,
        &[vmir::TrigTerm::Capture(0), vmir::TrigTerm::Bound(0)],
        "trigger is g(capture x, bound i)"
    );

    // The method body calls the occurrence with one argument (the captured x).
    let m_id = p.id("m").expect("missing method m");
    let vmir::Declaration::Method(m) = &p.decls[m_id] else {
        panic!("m must be a Method");
    };
    assert!(
        m.insts.iter().any(|i| matches!(
            &i.kind,
            vmir::InstKind::Pure(_, vmir::PureInst::FunctionCall(fc))
                if fc.function == q_id && fc.args.iter().count() == 1
        )),
        "method body must call the occurrence with the captured value"
    );
}

#[test]
fn nested_trigger_lowers_to_nested_app() {
    // A trigger may be an arbitrarily nested application: `{f(g(i))}` binds the
    // binder at depth 1.
    let input = r#"
domain D {
    function g(i: Int): Int
    function f(i: Int): Bool
    axiom nested { forall i: Int :: {f(g(i))} f(g(i)) }
}
"#;
    let p = run(input);
    let vmir::Declaration::Quantifier(q) = &p.decls[p.id("nested#quant0").unwrap()] else {
        panic!("nested#quant0 must be a Quantifier");
    };
    let f_id = p.id("f").expect("missing f");
    let g_id = p.id("g").expect("missing g");
    let (head, args) = only_app(only_group(q));
    assert_eq!(*head, vmir::TrigHead::Func(f_id));
    assert_eq!(
        args,
        &[vmir::TrigTerm::App {
            head: vmir::TrigHead::Func(g_id),
            type_args: Vec::new(),
            args: Box::new([vmir::TrigTerm::Bound(0)]),
        }],
        "trigger is f(g(i)) — the binder sits under the nested call"
    );
}

#[test]
fn multi_term_trigger_group_keeps_both_terms() {
    // `{f(i), g(i)}` is one group with two terms — a conjunctive multi-pattern.
    let input = r#"
domain D {
    function f(i: Int): Bool
    function g(i: Int): Bool
    axiom both { forall i: Int :: {f(i), g(i)} f(i) == g(i) }
}
"#;
    let p = run(input);
    let vmir::Declaration::Quantifier(q) = &p.decls[p.id("both#quant0").unwrap()] else {
        panic!("both#quant0 must be a Quantifier");
    };
    let group = only_group(q);
    assert_eq!(group.terms.len(), 2, "one group, two terms");
    let heads: Vec<_> = group
        .terms
        .iter()
        .map(|t| match t {
            vmir::TrigTerm::App { head, .. } => head.clone(),
            _ => panic!("terms must be applications"),
        })
        .collect();
    assert_eq!(
        heads,
        vec![
            vmir::TrigHead::Func(p.id("f").unwrap()),
            vmir::TrigHead::Func(p.id("g").unwrap()),
        ]
    );
}

#[test]
fn alternative_trigger_groups_all_kept() {
    // `{f(i)}{g(i)}` are alternatives: both groups reach VMIR (the verifier mints
    // one instantiation rule per group), none is silently dropped.
    let input = r#"
domain D {
    function f(i: Int): Bool
    function g(i: Int): Bool
    axiom alt { forall i: Int :: {f(i)}{g(i)} f(i) == g(i) }
}
"#;
    let p = run(input);
    let vmir::Declaration::Quantifier(q) = &p.decls[p.id("alt#quant0").unwrap()] else {
        panic!("alt#quant0 must be a Quantifier");
    };
    assert_eq!(q.triggers.len(), 2, "two alternative groups");
    for (group, name) in q.triggers.iter().zip(["f", "g"]) {
        let (head, args) = only_app(group);
        assert_eq!(*head, vmir::TrigHead::Func(p.id(name).unwrap()));
        assert_eq!(args, &[vmir::TrigTerm::Bound(0)]);
    }
}

#[test]
fn trigger_literal_argument_lowers_to_lit() {
    // A literal is a legal trigger argument, as long as the group still covers
    // every binder.
    let input = r#"
domain D {
    function f(i: Int, j: Int): Bool
    axiom lit { forall i: Int :: {f(i, 0)} f(i, 0) }
}
"#;
    let p = run(input);
    let vmir::Declaration::Quantifier(q) = &p.decls[p.id("lit#quant0").unwrap()] else {
        panic!("lit#quant0 must be a Quantifier");
    };
    let (_, args) = only_app(only_group(q));
    assert_eq!(
        args,
        &[
            vmir::TrigTerm::Bound(0),
            vmir::TrigTerm::Lit(vmir::Literal::Int(0.into())),
        ]
    );
}

#[test]
fn nested_forall_lowers() {
    // An inner `forall` captures the outer binder: it lowers to a second
    // quantifier with one capture param, whose occurrence call inside the outer
    // body passes the outer binder.
    let input = r#"
domain D {
    function g(i: Int, j: Int): Bool
    axiom nest { forall i: Int :: {g(i, i)} (forall j: Int :: {g(i, j)} g(i, j)) }
}
"#;
    let p = run(input);
    let outer_id = p.id("nest#quant0").expect("missing outer quantifier");
    let inner_id = p.id("nest#quant1").expect("missing inner quantifier");
    let vmir::Declaration::Quantifier(outer) = &p.decls[outer_id] else {
        panic!("nest#quant0 must be a Quantifier");
    };
    let vmir::Declaration::Quantifier(inner) = &p.decls[inner_id] else {
        panic!("nest#quant1 must be a Quantifier");
    };

    // Outer: no captures, one binder, trigger g(i, i).
    assert!(outer.params.is_empty(), "outer captures nothing");
    assert_eq!(outer.bound.len(), 1);
    assert_eq!(
        only_app(only_group(outer)).1,
        &[vmir::TrigTerm::Bound(0), vmir::TrigTerm::Bound(0)]
    );
    // The outer body calls the inner occurrence with the outer binder
    // (`Temp(0)`) as its capture argument.
    assert!(
        outer.body.insts.iter().any(|i| matches!(
            &i.kind,
            vmir::InstKind::Pure(_, vmir::PureInst::FunctionCall(fc))
                if fc.function == inner_id && fc.args.iter().eq(&[vmir::Val::Temp(0)])
        )),
        "outer body must call the inner occurrence with the outer binder"
    );

    // Inner: one capture (i: Int), one binder (j), mixed trigger g(i, j) =
    // [Capture(0), Bound(0)].
    assert_eq!(&*inner.params, &[vmir::Type::Int], "inner captures i");
    assert_eq!(inner.bound.len(), 1);
    assert_eq!(
        only_app(only_group(inner)).1,
        &[vmir::TrigTerm::Capture(0), vmir::TrigTerm::Bound(0)]
    );

    // The axiom body still references the outer occurrence via a nullary call.
    let ax_id = p.id("nest").expect("missing axiom nest");
    let vmir::Declaration::Axiom(ax) = &p.decls[ax_id] else {
        panic!("nest must be a Axiom");
    };
    assert!(
        ax.body.insts.iter().any(|i| matches!(
            &i.kind,
            vmir::InstKind::Pure(_, vmir::PureInst::FunctionCall(fc))
                if fc.function == outer_id && fc.args.iter().next().is_none()
        )),
        "axiom body must call the nullary outer occurrence"
    );

    // Display path must not panic and should render the capture param.
    let s = format!("{p}");
    assert!(
        s.contains("quantifier nest#quant1(e0: Int)"),
        "rendered:\n{s}"
    );
}

#[test]
fn nested_forall_slot_order() {
    // Flat preorder ids across nesting: a nested `forall` takes the slot after
    // its encloser; a later sibling top-level `forall` takes the next one. The
    // id-keyed slot fill must pair each declaration correctly even though the
    // inner quantifier finishes building before the outer.
    let input = r#"
domain D {
    function g(i: Int, j: Int): Bool
    function h(k: Int): Bool
    axiom ord {
        (forall i: Int :: {g(i, i)} (forall j: Int :: {g(i, j)} g(i, j)))
        && (forall k: Int :: {h(k)} h(k))
    }
}
"#;
    let p = run(input);
    let g_id = p.id("g").expect("missing g");
    let h_id = p.id("h").expect("missing h");
    let quant = |name: &str| {
        let id = p.id(name).unwrap_or_else(|| panic!("missing {name}"));
        match &p.decls[id] {
            vmir::Declaration::Quantifier(q) => q,
            _ => panic!("{name} must be a Quantifier"),
        }
    };
    // #quant0 = outer (trigger g, no captures), #quant1 = inner (trigger g,
    // one capture), #quant2 = sibling (trigger h).
    let head = |name: &str| only_app(only_group(quant(name))).0.clone();
    assert_eq!(head("ord#quant0"), vmir::TrigHead::Func(g_id));
    assert!(quant("ord#quant0").params.is_empty());
    assert_eq!(head("ord#quant1"), vmir::TrigHead::Func(g_id));
    assert_eq!(quant("ord#quant1").params.len(), 1);
    assert_eq!(head("ord#quant2"), vmir::TrigHead::Func(h_id));
    assert!(quant("ord#quant2").params.is_empty());
}
