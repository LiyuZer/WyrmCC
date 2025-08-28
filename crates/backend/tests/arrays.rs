use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn alloca_int_array_decl() {
    // int main(void){ int a[3]; return 0; }
    let src = r#"
        int main(void) {
            int a[3];
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect stack allocation for the array type
    assert!(ir.contains("%a = alloca [3 x i32]"), "expected alloca for int a[3], IR:\n{}", ir);
}

#[test]
fn index_store_and_load_from_array() {
    // int main(void){ int a[3]; a[0]=1; a[1]=2; return a[0] + a[1]; }
    let src = r#"
        int main(void) {
            int a[3];
            a[0] = 1;
            a[1] = 2;
            return a[0] + a[1];
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Allocation present
    assert!(ir.contains("%a = alloca [3 x i32]"), "expected alloca for a[3], IR:\n{}", ir);

    // Expect to see GEPs either directly from the array or from a decayed pointer
    let has_array_gep = ir.contains("getelementptr inbounds [3 x i32]");
    let has_i32_gep = ir.contains("getelementptr inbounds i32, ptr");
    assert!(has_array_gep || has_i32_gep, "expected GEPs for array indexing (either [3 x i32] or i32), IR:\n{}", ir);

    // Expect stores for a[0] and a[1]
    assert!(ir.contains("store i32 1, ptr"), "expected store of 1 into a[0], IR:\n{}", ir);
    assert!(ir.contains("store i32 2, ptr"), "expected store of 2 into a[1], IR:\n{}", ir);

    // Expect loads when computing return value
    assert!(ir.contains("load i32, ptr"), "expected loads from array elements, IR:\n{}", ir);
}
