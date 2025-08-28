use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn emit_string_and_puts() {
    let src = r#"
        int main(void) { puts("hi"); return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Must declare puts with ptr parameter
    assert!(
        ir.contains("declare i32 @puts(ptr)"),
        "missing puts declaration in IR:\n{}",
        ir
    );

    // Should contain a private unnamed_addr string global and a GEP to it
    assert!(
        ir.contains("private unnamed_addr constant ["),
        "missing string global in IR:\n{}",
        ir
    );
    assert!(
        ir.contains("getelementptr inbounds"),
        "missing GEP to string data in IR:\n{}",
        ir
    );

    // Call to puts should pass a ptr argument
    assert!(
        ir.contains("call i32 @puts(") && ir.contains("ptr %"),
        "missing call to puts with ptr arg in IR:\n{}",
        ir
    );
}
