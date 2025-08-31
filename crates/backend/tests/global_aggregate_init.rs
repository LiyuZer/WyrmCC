use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn global_struct_of_ints_initializer() {
    // struct S { int a; int b; }; struct S g = {1,2}; int main(){return 0;}
    let src = r#"
        struct S { int a; int b; };
        struct S g = {1,2};
        int main(void) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect a global for g with a constant struct of two i32 values 1 and 2
    let ok = ir.contains("@g =")
        && (
            ir.contains("{ i32, i32 } { i32 1, i32 2 }")
            || (ir.contains("i32 1") && ir.contains("i32 2") && ir.contains("@g =") && ir.contains("global"))
        );
    assert!(ok, "IR did not show struct-of-ints initializer.\nIR:\n{}", ir);
}

#[test]
fn global_char_array_from_string_unsized_and_sized() {
    // char s1[] = "hi"; char s2[3] = "hi"; int main(){return 0;}
    let src = r#"
        char s1[] = "hi";
        char s2[3] = "hi";
        int main(void) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect both globals present and sized to 3 bytes including NUL
    // Accept either c"hi\\00" or explicit byte list
    let s1_ok = ir.contains("@s1 =") && ir.contains("[3 x i8]")
        && (ir.contains("c\"hi\\00\"") || ir.contains("i8 104") && ir.contains("i8 105") && ir.contains("i8 0"));
    let s2_ok = ir.contains("@s2 =") && ir.contains("[3 x i8]")
        && (ir.contains("c\"hi\\00\"") || ir.contains("i8 104") && ir.contains("i8 105") && ir.contains("i8 0"));

    assert!(s1_ok, "IR did not contain expected s1 string initializer.\nIR:\n{}", ir);
    assert!(s2_ok, "IR did not contain expected s2 string initializer.\nIR:\n{}", ir);
}
