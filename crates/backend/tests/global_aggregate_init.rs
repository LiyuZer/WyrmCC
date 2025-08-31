use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn global_struct_init_constant() {
    // struct S { int a; int b; }; struct S g = {1,2};
    let src = r#"
        struct S { int a; int b; };
        struct S g = {1,2};
        int main(void) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect a global for g with a struct type and constant fields 1 and 2
    assert!(
        ir.contains("@g = global") &&
        (ir.contains("{ i32, i32 }") || ir.contains("%struct.S")) &&
        ir.contains("i32 1") &&
        ir.contains("i32 2"),
        "IR did not contain expected global struct initializer.\nIR:\n{}",
        ir
    );
}

#[test]
fn global_char_array_from_string_constant() {
    // char s[] = "hi"; expect a private constant string or inline c"hi\00" in global
    let src = r#"
        char s[] = "hi";
        int main(void) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect global [3 x i8] with c"hi\00" or explicit bytes
    let ok = (
        ir.contains("@s =") && ir.contains("[3 x i8]") &&
        (ir.contains("c\"hi\\00\"") || ir.contains("i8 104") || ir.contains("i8 0"))
    );
    assert!(ok, "IR did not contain expected global char[] from string.\nIR:\n{}", ir);
}
