use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn local_array_init_memset_and_stores() {
    // int main(void){ int a[3] = {1,2,3}; return 0; }
    let src = r#"
        int main(void) {
            int a[3] = {1,2,3};
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect stack allocation for the array
    assert!(
        ir.contains("%a = alloca [3 x i32]") || ir.contains("alloca [3 x i32], ptr %a"),
        "expected alloca for int a[3], IR:\n{}",
        ir
    );

    // Expect memset(0, size)
    assert!(
        ir.contains("@llvm.memset"),
        "expected a call to @llvm.memset to zero-initialize local aggregate, IR:\n{}",
        ir
    );

    // Expect stores for the three elements 1, 2, 3
    assert!(ir.contains("store i32 1, ptr"), "expected store 1, IR:\n{}", ir);
    assert!(ir.contains("store i32 2, ptr"), "expected store 2, IR:\n{}", ir);
    assert!(ir.contains("store i32 3, ptr"), "expected store 3, IR:\n{}", ir);
}

#[test]
fn local_struct_init_memset_and_field_stores() {
    // struct S { int a; int b; }; int main(){ struct S s = {1,2}; return 0; }
    let src = r#"
        int main(void) {
            struct S { int a; int b; };
            struct S s = {1,2};
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect alloca for struct (type name may vary)
    assert!(
        ir.contains("alloca %struct.S") || ir.contains("alloca { i32, i32 }") || ir.contains("%s = alloca"),
        "expected alloca for struct S, IR:\n{}",
        ir
    );

    // Expect memset then two stores of i32 values
    assert!(ir.contains("@llvm.memset"), "expected memset for struct zero-fill, IR:\n{}", ir);
    assert!(ir.contains("store i32 1, ptr"), "expected store of 1 into field, IR:\n{}", ir);
    assert!(ir.contains("store i32 2, ptr"), "expected store of 2 into field, IR:\n{}", ir);
}

#[test]
fn local_nested_struct_with_array_field_init_memset_and_stores() {
    // struct T{ int a[2]; int b; }; int main(){ struct T t = {{1,2}, 3}; return 0; }
    let src = r#"
        int main(void) {
            struct T { int a[2]; int b; };
            struct T t = { {1,2}, 3 };
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect alloca for struct T
    assert!(
        ir.contains("alloca %struct.T") || ir.contains("%t = alloca"),
        "expected alloca for struct T, IR:\n{}",
        ir
    );

    // Expect memset for zero-initialization
    assert!(ir.contains("@llvm.memset"), "expected memset for struct T, IR:\n{}", ir);

    // Expect stores for a[0]=1, a[1]=2, and b=3
    assert!(ir.contains("store i32 1, ptr"), "expected store 1 to t.a[0], IR:\n{}", ir);
    assert!(ir.contains("store i32 2, ptr"), "expected store 2 to t.a[1], IR:\n{}", ir);
    assert!(ir.contains("store i32 3, ptr"), "expected store 3 to t.b, IR:\n{}", ir);
}

#[test]
fn local_char_array_from_string_memcpy() {
    // int main(){ char s[3] = "hi"; return 0; }
    // Expect a memcpy of 3 bytes (including NUL) from a constant string to the stack buffer.
    let src = r#"
        int main(void) {
            char s[3] = "hi";
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect alloca for [3 x i8]
    assert!(
        ir.contains("alloca [3 x i8]") || ir.contains("%s = alloca [3 x i8]"),
        "expected alloca for char s[3], IR:\n{}",
        ir
    );

    // Expect a memcpy from a constant string (look for memcpy and a private constant string)
    assert!(ir.contains("@llvm.memcpy"), "expected memcpy for string copy, IR:\n{}", ir);
    assert!(ir.contains("private unnamed_addr constant") || ir.contains("c\"hi\\00\""),
        "expected presence of constant string source, IR:\n{}",
        ir);
}
