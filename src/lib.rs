pub mod silver;
pub mod translate;
mod util;
// pub mod verify;
pub mod vmir;
pub use silver::silver_parser;
pub use util::*;

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
