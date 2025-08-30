use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn ptr_subtraction_ir_patterns() {
    // int main(void){ int arr[10]; int *p=&arr[2]; int *q=&arr[7]; return q - p; }
    let src = r#"
        int main(void) {
            int arr[10];
            int *p = &arr[2];
            int *q = &arr[7];
            return q - p;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect pointer subtraction to be lowered via ptrtoint -> i64, sub i64, divide by element size (4), then trunc to i32
    assert!(
        ir.contains("ptrtoint ptr "),
        "expected ptrtoint from ptr to integer in IR, got:\n{}",
        ir
    );
    assert!(
        ir.contains(" sub i64 ") || ir.contains("= sub i64"),
        "expected sub i64 for pointer difference in IR, got:\n{}",
        ir
    );
    assert!(
        ir.contains("sdiv i64") && ir.contains(", 4"),
        "expected sdiv i64 by 4 (sizeof(int)) in IR, got:\n{}",
        ir
    );
    assert!(
        ir.contains("trunc i64") || ir.contains("to i32"),
        "expected truncation to i32 for return value, IR:\n{}",
        ir
    );
}
