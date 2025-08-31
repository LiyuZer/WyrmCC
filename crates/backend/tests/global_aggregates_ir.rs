use backend::{emit_llvm_ir, verify_llvm_text};
use parse::parse_translation_unit;

#[test]
fn global_array_const_ir() {
    let src = r#"
        int a[3] = {1,2,3};
        int main(void) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "mod").expect("emit ok");
    verify_llvm_text(&ir).expect("llvm text verifies");
    assert!(ir.contains("@a = global [3 x i32] [ i32 1, i32 2, i32 3 ]"), "IR did not contain expected global array:\n{}", ir);
}

#[test]
fn global_array_2d_const_ir() {
    let src = r#"
        int b[2][2] = { {1,2}, {3,4} };
        int main(void) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "mod").expect("emit ok");
    verify_llvm_text(&ir).expect("llvm text verifies");
    assert!(ir.contains("@b = global [2 x [2 x i32]]"), "IR missing 2D array type:\n{}", ir);
    assert!(ir.contains("[2 x i32] [ i32 1, i32 2 ]"), "IR missing first row init:\n{}", ir);
    assert!(ir.contains("[2 x i32] [ i32 3, i32 4 ]"), "IR missing second row init:\n{}", ir);
}

#[test]
fn global_char_string_ir() {
    let src = r#"
        char s[3] = "hi";
        int main(void) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "mod").expect("emit ok");
    verify_llvm_text(&ir).expect("llvm text verifies");
    // Expect c"hi\\00"
    assert!(ir.contains("@s = global [3 x i8] c\"hi\\00\""), "IR did not contain expected char array from string:\n{}", ir);
}

#[test]
fn global_struct_const_ir() {
    let src = r#"
        struct S { int x; int y; };
        struct S s = {1,2};
        int main(void) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "mod").expect("emit ok");
    verify_llvm_text(&ir).expect("llvm text verifies");
    assert!(ir.contains("@s = global { i32, i32 } { i32 1, i32 2 }"), "IR did not contain expected struct constant:\n{}", ir);
}
