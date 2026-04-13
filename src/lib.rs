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

    #[test]
    fn test_simple_method_translation() {
        let input = r#"
method test(x: Int) returns (y: Int)
{
  y := x
}
"#;
        let program = silver::silver_parser::sil_program(input).expect("Parse failed");
        let vmir = translate::VmirTranslator::translate(&program).expect("Translation failed");
        println!("{}", vmir);
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
