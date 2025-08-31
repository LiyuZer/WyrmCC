use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn printf_decl_and_ptr_and_int_args_typed() {
    // int main(void){ int x=0; int *p=&x; printf("%p %d\n", p, 42); return 0; }
    // No explicit prototype: backend should auto-declare printf(ptr, ...)
    let src = r#"
        int main(void) {
            int x = 0;
            int *p = &x;
            printf("%p %d\n", p, 42);
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Declaration for printf should be varargs with first arg ptr
    assert!(
        ir.contains("declare i32 @printf(ptr, ...)")
            || ir.contains("declare i32 @printf(ptr , ...)"),
        "expected printf declaration with ptr, ...; IR:\n{}",
        ir
    );

    // Ensure we emit a call to printf
    assert!(
        ir.contains("call i32 @printf("),
        "expected a call to printf in IR, got:\n{}",
        ir
    );

    // First argument (format) should be typed as ptr; allow either on decl or call line
    assert!(
        ir.contains("@printf(ptr "),
        "expected first printf arg typed ptr (format string), IR:\n{}",
        ir
    );

    // Subsequent arguments: pointer vararg as ptr, integer vararg as i32
    assert!(
        ir.contains(", ptr ") && ir.contains(", i32 42"),
        "expected ptr and i32 typed arguments in the printf call, IR:\n{}",
        ir
    );
}
