use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn set_and_get_2d() {
    // int main(void){ int a[2][3]; a[1][2] = 7; return a[1][2]; }
    let src = r#"
        int main(void) {
            int a[2][3];
            a[1][2] = 7;
            return a[1][2];
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect nested array allocation
    assert!(
        ir.contains("%a = alloca [2 x [3 x i32]"),
        "expected alloca for int a[2][3], IR:\n{}",
        ir
    );

    // Expect we index into the array (presence of GEP)
    assert!(
        ir.contains("getelementptr inbounds"),
        "expected GEPs for multidimensional indexing, IR:\n{}",
        ir
    );

    // Expect a store of 7 and a load/ret path
    assert!(ir.contains("store i32 7, ptr"), "expected store of 7 into a[1][2], IR:\n{}", ir);
    assert!(ir.contains("ret i32"), "expected function to return an i32, IR:\n{}", ir);
}

#[test]
fn pointer_to_row_then_index() {
    // int main(void){ int a[2][3]; int *p; p = &a[1][0]; p[2] = 5; return a[1][2]; }
    let src = r#"
        int main(void) {
            int a[2][3];
            int *p;
            p = &a[1][0];
            p[2] = 5;
            return a[1][2];
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect nested array allocation still
    assert!(
        ir.contains("%a = alloca [2 x [3 x i32]"),
        "expected alloca for int a[2][3], IR:\n{}",
        ir
    );

    // Expect GEPs present for row address and element indexing
    assert!(
        ir.contains("getelementptr inbounds"),
        "expected GEPs for &a[1][0] and p[2], IR:\n{}",
        ir
    );

    // Expect store of 5 through pointer and return path
    assert!(ir.contains("store i32 5, ptr"), "expected store of 5 via p[2], IR:\n{}", ir);
    assert!(ir.contains("ret i32"), "expected function to return an i32, IR:\n{}", ir);
}
