use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn emit_params_signature_and_prologue() {
    let src = r#"
        int add(int a, int b) {
            return a + b;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Function signature includes parameters
    assert!(
        ir.contains("define i32 @add(i32 %a, i32 %b)"),
        "IR missing function signature with parameters:\n{}",
        ir
    );

    // Prologue stores incoming args into allocas named %a.addr / %b.addr
    assert!(
        ir.contains("%a.addr = alloca i32"),
        "missing a.addr alloca:\n{}",
        ir
    );
    assert!(
        ir.contains("store i32 %a, ptr %a.addr"),
        "missing store of %a to %a.addr:\n{}",
        ir
    );
    assert!(
        ir.contains("%b.addr = alloca i32"),
        "missing b.addr alloca:\n{}",
        ir
    );
    assert!(
        ir.contains("store i32 %b, ptr %b.addr"),
        "missing store of %b to %b.addr:\n{}",
        ir
    );

    // Body should perform an add (loads + add)
    assert!(ir.contains(" add i32 "), "missing add instruction:\n{}", ir);
}

#[test]
fn emit_call_with_args() {
    let src = r#"
        int add(int a, int b) { return a + b; }
        int main(void) { return add(2, 40); }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Ensure the call uses two i32 arguments with constants
    assert!(
        ir.contains("call i32 @add(i32 2, i32 40)"),
        "missing call to add with args 2 and 40:\n{}",
        ir
    );
}
