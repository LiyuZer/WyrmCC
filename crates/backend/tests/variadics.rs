use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn variadic_function_header() {
    let src = r#"
        int sum(int a, ...) { return a; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Function signature includes variadic ellipsis after named params
    assert!(
        ir.contains("define i32 @sum(i32 %a, ...)"),
        "IR missing variadic function signature with parameters and ellipsis:\n{}",
        ir
    );

    // Prologue still stores incoming named arg into alloca
    assert!(ir.contains("%a.addr = alloca i32"), "missing a.addr alloca:\n{}", ir);
    assert!(
        ir.contains("store i32 %a, ptr %a.addr"),
        "missing store of %a to %a.addr:\n{}",
        ir
    );
}

#[test]
fn variadic_call_shape() {
    let src = r#"
        int sum(int a, ...) { return a; }
        int main(void) { return sum(2, 40, 0); }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Ensure the call passes extra i32 arguments; backend uses i32 for ints
    assert!(
        ir.contains("call i32 @sum(i32 2, i32 40, i32 0)"),
        "missing call to sum with extra args 40 and 0:\n{}",
        ir
    );
}
