use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn indirect_call_through_conditional_pointer() {
    let src = r#"
        int add(int a, int b) { return a + b; }
        int sub(int a, int b) { return a - b; }
        int main(void) {
            int x = 1;
            // Select a function pointer at runtime, then call it
            return (* (x ? &add : &sub))(10, 3);
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "indirect").expect("emit ok");

    // Should contain definitions for add and sub
    assert!(ir.contains("define i32 @add("), "expected add definition in IR:\n{}", ir);
    assert!(ir.contains("define i32 @sub("), "expected sub definition in IR:\n{}", ir);

    // Expect an indirect call site (callee is a value, not a symbol); with opaque pointers this looks like 'call i32 %...'
    assert!(ir.contains("call i32 %"), "expected an indirect call (callee as %reg) in IR:\n{}", ir);
}
