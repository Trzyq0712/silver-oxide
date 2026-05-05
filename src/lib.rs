pub mod silver;
pub mod translate;
mod util;
pub mod vmir;
pub use silver::silver_parser;
pub use util::*;

#[cfg(test)]
mod tests {
    use crate::{silver, translate, vmir};

    #[test]
    fn first_example_emits_method_contract_resources() {
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

        let program = silver::silver_parser::sil_program(input).expect("parse failed");
        let vmir = translate::VmirTranslator::translate(&program).expect("translation failed");

        for name in [
            "assign@ensures",
            "read@requires",
            "read@ensures",
            "add@requires",
            "add@ensures",
        ] {
            let id = vmir
                .interner
                .get(name)
                .unwrap_or_else(|| panic!("missing resource name: {name}"));
            assert!(
                matches!(vmir.decls[id], vmir::Declaration::Resource(_)),
                "{name} must be translated as Resource"
            );
        }
        assert!(
            vmir.interner.get("assign@requires").is_none(),
            "assign has no precondition, so assign@requires must not be generated"
        );
    }

    #[test]
    fn add_method_uses_heap_arithmetic_and_checks_for_contract_application() {
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

        let program = silver::silver_parser::sil_program(input).expect("parse failed");
        let vmir = translate::VmirTranslator::translate(&program).expect("translation failed");
        let add_id = vmir.interner.get("add").expect("missing add method");
        let vmir::Declaration::Method(add) = &vmir.decls[add_id] else {
            panic!("add declaration must be a method");
        };

        let saw_heap_add = add
            .insts
            .iter()
            .any(|inst| matches!(inst, vmir::Inst::Heap(vmir::HeapInst::Add(_, _))));
        let saw_heap_sub = add
            .insts
            .iter()
            .any(|inst| matches!(inst, vmir::Inst::Heap(vmir::HeapInst::Sub(_, _))));
        let saw_assume = add
            .insts
            .iter()
            .any(|inst| matches!(inst, vmir::Inst::Assume(_)));
        let saw_assert = add
            .insts
            .iter()
            .any(|inst| matches!(inst, vmir::Inst::Assert(_)));

        assert!(saw_heap_add, "expected heap addition in add translation");
        assert!(saw_heap_sub, "expected heap subtraction in add translation");
        assert!(saw_assume, "expected assume checks in add translation");
        assert!(saw_assert, "expected assert checks in add translation");
    }

    #[test]
    fn add_ensures_resource_builds_heap_via_acc_and_add_with_param_offset() {
        let input = r#"
predicate number(this: Ref)

method add(this: Ref, other: Ref) returns (res: Ref)
  requires number(this) && number(other)
  ensures number(this) && number(other) && number(res)
{
}
"#;
        let program = silver::silver_parser::sil_program(input).expect("parse failed");
        let vmir = translate::VmirTranslator::translate(&program).expect("translation failed");
        let ensures_id = vmir
            .interner
            .get("add@ensures")
            .expect("missing add@ensures");
        let vmir::Declaration::Resource(ensures) = &vmir.decls[ensures_id] else {
            panic!("add@ensures must be a resource");
        };

        assert_eq!(ensures.params.len(), 3);
        assert!(
            ensures
                .insts
                .iter()
                .any(|i| matches!(i, vmir::Inst::Heap(vmir::HeapInst::Acc(_)))),
            "add@ensures must contain acc heap construction"
        );
        assert!(
            ensures
                .insts
                .iter()
                .any(|i| matches!(i, vmir::Inst::Heap(vmir::HeapInst::Add(_, _)))),
            "add@ensures must contain heap additions"
        );
        match ensures.res.0 {
            vmir::HeapVal::Temp(idx) => assert!(
                idx >= ensures.params.len(),
                "resource result heap temp must be offset after params"
            ),
            vmir::HeapVal::Empty => panic!("add@ensures must return constructed heap, not empty"),
            vmir::HeapVal::Implicit => panic!("unexpected implicit heap result"),
        }
    }

    #[test]
    fn methods_without_body_do_not_emit_vmir_method_and_missing_contracts_do_not_emit_resources() {
        let input = r#"
method sig_only(a: Int)

method only_pre(x: Int)
  requires x < 1

method only_post(x: Int)
  ensures x == x
"#;
        let program = silver::silver_parser::sil_program(input).expect("parse failed");
        let vmir = translate::VmirTranslator::translate(&program).expect("translation failed");

        let sig_only = vmir.interner.get("sig_only").expect("missing sig_only");
        assert!(
            !matches!(vmir.decls[sig_only], vmir::Declaration::Method(_)),
            "body-less methods must not emit VMIR Method declarations"
        );

        assert!(
            vmir.interner.get("sig_only@requires").is_none(),
            "method without precondition should not emit @requires resource"
        );
        assert!(
            vmir.interner.get("sig_only@ensures").is_none(),
            "method without postcondition should not emit @ensures resource"
        );

        let only_pre_req = vmir
            .interner
            .get("only_pre@requires")
            .expect("missing only_pre@requires");
        assert!(matches!(
            vmir.decls[only_pre_req],
            vmir::Declaration::Resource(_)
        ));
        assert!(
            vmir.interner.get("only_pre@ensures").is_none(),
            "method without postcondition should not emit @ensures resource"
        );

        let only_post_ens = vmir
            .interner
            .get("only_post@ensures")
            .expect("missing only_post@ensures");
        assert!(matches!(
            vmir.decls[only_post_ens],
            vmir::Declaration::Resource(_)
        ));
        assert!(
            vmir.interner.get("only_post@requires").is_none(),
            "method without precondition should not emit @requires resource"
        );
    }
}
