use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn short_ptr_subtraction_scales_by_2() {
    // int main(void){ short arr[10]; short *p=&arr[2]; short *q=&arr[7]; return q - p; }
    let src = r#"
        int main(void) {
            short arr[10];
            short *p = &arr[2];
            short *q = &arr[7];
            return q - p;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect pointer subtraction to be lowered via ptrtoint -> i64, sub i64,
    // divide by element size (2 for short), then trunc to i32
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
        ir.contains("sdiv i64") && ir.contains(", 2"),
        "expected sdiv i64 by 2 (sizeof(short)) in IR, got:\n{}",
        ir
    );
    assert!(
        ir.contains("trunc i64") || ir.contains("to i32"),
        "expected truncation to i32 for return value, IR:\n{}",
        ir
    );
}

#[test]
fn char_ptr_subtraction_checks() {
    // int main(void){ char arr[10]; char *p=&arr[2]; char *q=&arr[7]; return q - p; }
    let src = r#"
        int main(void) {
            char arr[10];
            char *p = &arr[2];
            char *q = &arr[7];
            return q - p;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // For char (size 1), the division by 1 may be optimized away; we still
    // expect ptrtoint + sub sequence and truncation to i32.
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
        ir.contains("trunc i64") || ir.contains("to i32"),
        "expected truncation to i32 for return value, IR:\n{}",
        ir
    );
}
