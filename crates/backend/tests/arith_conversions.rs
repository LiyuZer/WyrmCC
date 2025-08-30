use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn shr_is_arithmetic_for_int() {
    let src = r#"
        int f() { int x = -2; return x >> 1; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");
    assert!(
        ir.contains("ashr"),
        "IR should use arithmetic shift right for >> on int:\n{}",
        ir
    );
}

#[test]
fn sdiv_and_srem_present_for_negatives() {
    let src = r#"
        int f() { return (-7 / 3) + (-7 % 3); }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");
    assert!(ir.contains("sdiv"), "IR should use sdiv for division:\n{}", ir);
    assert!(ir.contains("srem"), "IR should use srem for modulo:\n{}", ir);
}

#[test]
fn ptr_minus_var_index_uses_zext_and_sub_for_gep() {
    let src = r#"
        int f() {
            int a[5];
            int *p = a;
            int i = 2;
            return *(p - i);
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");
    // Dynamic index should be extended to i64 for GEP scaling
    assert!(ir.contains("zext i32"), "IR should zext index to i64:\n{}", ir);
    // For p - i, we negate the idx64 via `sub i64 0, <idx64>`
    assert!(
        ir.contains("sub i64 0"),
        "IR should negate idx via sub i64 0, idx64 for p - i:\n{}",
        ir
    );
    // Ensure we form a GEP in terms of i32 elements
    assert!(
        ir.contains("getelementptr inbounds i32, ptr"),
        "IR should use GEP on i32 element type:\n{}",
        ir
    );
}
