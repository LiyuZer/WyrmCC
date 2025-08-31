use backend::emit_llvm_ir;

#[test]
fn global_int_array_init_ir() {
    let src = r#"
        int g[3] = {1,2,3};
        int main(void) { return 0; }
    "#;
    let tu = parse::parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "arr_init").expect("emit ok");
    // Expect a typed global array with explicit elements
    assert!(
        ir.contains("@g =") && ir.contains("[3 x i32]") && ir.contains("i32 1") && ir.contains("i32 2") && ir.contains("i32 3"),
        "IR did not contain expected global array initializer.\nIR:\n{}",
        ir
    );
}

#[test]
fn global_int_array_zerofill_ir() {
    let src = r#"
        int g2[5] = {1,2};
        int main(void) { return 0; }
    "#;
    let tu = parse::parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "arr_init2").expect("emit ok");
    // Accept either explicit zero padding or overall zeroinitializer after elements
    let ok = (ir.contains("@g2 =") && ir.contains("[5 x i32]") && ir.contains("i32 1") && ir.contains("i32 2") && ir.contains("i32 0"))
        || (ir.contains("@g2 =") && ir.contains("[5 x i32]") && ir.contains("zeroinitializer"));
    assert!(ok, "IR did not show zero-fill behavior for partial initializer.\nIR:\n{}", ir);
}
