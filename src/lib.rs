pub mod silver;
pub mod translate;
mod util;
// pub mod verify;
pub mod vmir;
pub use silver::silver_parser;
pub use util::*;

use crate::vmir::AccInst;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vmir::{Declaration, HeapExp, HeapInstKind, Literal, PureInst, Type, Value};

    fn heap_value_type(exp: &HeapExp, value: &Value) -> Option<Type> {
        match value {
            Value::Temp(t) if *t < exp.input_types.len() => Some(exp.input_types[*t].clone()),
            Value::Temp(t) => exp
                .insts
                .get(*t - exp.input_types.len())
                .map(|inst| inst.ty.clone()),
            Value::Literal(Literal::Bool(_)) => Some(Type::Bool),
            Value::Literal(Literal::Int(_)) => Some(Type::Int),
            Value::Literal(Literal::Real(_)) => Some(Type::Real),
            Value::Literal(Literal::Null) => Some(Type::Ref),
            Value::Literal(Literal::EmptyHeap) => Some(Type::Heap),
        }
    }

    #[test]
    fn test_simple_method_translation_uses_heapexp_contract_declarations() {
        let input = r#"
method test(x: Int) returns (y: Int)
  requires x > 0
  ensures y == x
{
  y := x
}
"#;
        let program = silver::silver_parser::sil_program(input).expect("Parse failed");
        let vmir = translate::VmirTranslator::translate(&program).expect("Translation failed");

        let method_id = vmir
            .interner
            .get("test")
            .expect("missing method declaration");
        let requires_id = vmir
            .interner
            .get("test@requires")
            .expect("missing requires declaration");
        let ensures_id = vmir
            .interner
            .get("test@ensures")
            .expect("missing ensures declaration");

        assert!(matches!(vmir.decls[method_id], Declaration::DomainElement));

        let Declaration::HeapExp(requires) = &vmir.decls[requires_id] else {
            panic!("test@requires must be a heap expression");
        };
        assert_eq!(requires.input_types, vec![Type::Heap, Type::Int]);

        let Declaration::HeapExp(ensures) = &vmir.decls[ensures_id] else {
            panic!("test@ensures must be a heap expression");
        };
        assert_eq!(
            ensures.input_types,
            vec![Type::Heap, Type::Heap, Type::Int, Type::Int]
        );
    }

    #[test]
    fn test_requires_predicate_conjunction_keeps_heapexp_types_sound() {
        let input = r#"
predicate number(x: Ref)

method add(this: Ref, other: Ref)
  requires number(this) && number(other)
{
}
"#;
        let program = silver::silver_parser::sil_program(input).expect("Parse failed");
        let vmir = translate::VmirTranslator::translate(&program).expect("Translation failed");

        let number_id = vmir
            .interner
            .get("number")
            .expect("missing predicate function declaration");
        let requires_id = vmir
            .interner
            .get("add@requires")
            .expect("missing add@requires declaration");
        let Declaration::HeapExp(requires) = &vmir.decls[requires_id] else {
            panic!("add@requires must be a heap expression");
        };

        let mut saw_number_call = false;
        let mut saw_acc = false;
        for inst in &requires.insts {
            match &inst.kind {
                HeapInstKind::Pure(PureInst::Call(func_id, _)) if *func_id == number_id => {
                    saw_number_call = true;
                    assert!(
                        matches!(inst.ty, Type::Addr(_)),
                        "predicate call must produce address type, got {:?}",
                        inst.ty
                    );
                }
                HeapInstKind::Acc(_) => {
                    saw_acc = true;
                    assert_eq!(inst.ty, Type::Heap, "acc instruction must produce heap");
                }
                _ => {}
            }
        }

        assert!(
            saw_number_call,
            "expected predicate function call(s) in requires"
        );
        assert!(saw_acc, "expected acc instruction(s) in requires");
        assert_eq!(
            heap_value_type(requires, &requires.res_pure),
            Some(Type::Bool),
            "final pure result should be Bool"
        );
    }
}

#[test]
fn test_field_access_method() {
    let input = std::fs::read_to_string("test_method.sil").expect("Failed to read file");
    let program = silver::silver_parser::sil_program(&input).expect("Parse failed");
    let vmir = translate::VmirTranslator::translate(&program).expect("Translation failed");
    println!("{}", vmir);
}

#[test]
fn test_var_initialization() {
    let input = r#"
method test() returns (y: Int)
{
  var x: Int := 5
  y := x
}
"#;
    let program = silver::silver_parser::sil_program(input).expect("Parse failed");
    let vmir = translate::VmirTranslator::translate(&program).expect("Translation failed");
    println!("{}", vmir);
}

#[test]
fn test_field_assignment() {
    let input = r#"
field value: Int

method test(this: Ref)
{
  this.value := 5
}
"#;
    let program = silver::silver_parser::sil_program(input).expect("Parse failed");
    let vmir = translate::VmirTranslator::translate(&program).expect("Translation failed");
    println!("{}", vmir);
}

#[test]
fn test_heap_assertion_forms_translation_smoke() {
    let input = r#"
field f: Int

method test(x: Ref)
  requires true
  requires acc(x.f)
  requires acc(x.f) && acc(x.f)
  requires x == null ? acc(x.f) : acc(x.f)
{
}
"#;
    let program = silver::silver_parser::sil_program(input).expect("Parse failed");
    let vmir = translate::VmirTranslator::translate(&program).expect("Translation failed");
    println!("{}", vmir);
}

#[test]
fn test_heap_ternary_acc_permissions_are_path_conditionalized_with_branch_polarity() {
    use vmir::{Declaration, HeapInstKind, Literal, PureInst, Value};

    fn real(n: i64) -> Value {
        Literal::Real(num::BigInt::from(n).into()).into()
    }

    let input = r#"
field f: Int

method test(path: Bool, x: Ref)
  requires path ? acc(x.f, write) : acc(x.f, write)
{
}
"#;
    let program = silver::silver_parser::sil_program(input).expect("Parse failed");
    let vmir = translate::VmirTranslator::translate(&program).expect("Translation failed");

    let requires_id = vmir
        .interner
        .get("test@requires")
        .expect("missing requires declaration");
    let Declaration::HeapExp(requires) = &vmir.decls[requires_id] else {
        panic!("test@requires must be a heap expression");
    };

    let arg_base = requires.input_types.len();
    let path_cond = Value::Temp(1);
    let zero = real(0);
    let one = real(1);

    let mut saw_positive = false;
    let mut saw_negative = false;

    for inst in &requires.insts {
        let HeapInstKind::Acc(AccInst { perm, .. }) = &inst.kind else {
            continue;
        };

        let Value::Temp(temp) = perm else {
            panic!("expected path-conditionalized acc amount temp, got {perm:?}");
        };
        assert!(
            *temp >= arg_base,
            "acc amount temp should come from an instruction"
        );
        let amt_inst = &requires.insts[*temp - arg_base];

        let HeapInstKind::Pure(PureInst::Ternary(cond, then_amt, else_amt)) = &amt_inst.kind else {
            panic!(
                "acc amount should come from ternary, got {:?}",
                amt_inst.kind
            );
        };
        assert_eq!(*cond, path_cond);

        if *then_amt == one && *else_amt == zero {
            saw_positive = true;
        } else if *then_amt == zero && *else_amt == one {
            saw_negative = true;
        } else {
            panic!("unexpected acc amount polarity ternary: then={then_amt:?}, else={else_amt:?}");
        }
    }

    assert!(
        saw_positive,
        "missing then-branch polarity (path ? perm : 0)"
    );
    assert!(
        saw_negative,
        "missing else-branch polarity (path ? 0 : perm)"
    );
}
