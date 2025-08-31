use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn comma_constant_rhs_returns_value() {
    // int main(void){ return (1, 2); }
    let src = r#"
        int main(void) {
            return (1, 2);
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");
    assert!(
        ir.contains("ret i32 2"),
        "expected ret i32 2 in IR, got:\n{}",
        ir
    );
}

#[test]
fn comma_assignment_then_value_stores_then_returns_rhs() {
    // int main(void){ int i=0; int r=(i=1, 2); return r; }
    let src = r#"
        int main(void) {
            int i = 0;
            int r = (i = 1, 2);
            return r;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");
    // Must store 1 into i, and ultimately store 2 into r; ensure return present
    assert!(
        ir.contains("store i32 1, ptr %i"),
        "expected store of 1 into %i, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("store i32 2, ptr %r"),
        "expected store of 2 into %r, IR:\n{}",
        ir
    );
    assert!(ir.contains("ret i32"), "expected a return, IR:\n{}", ir);
}
