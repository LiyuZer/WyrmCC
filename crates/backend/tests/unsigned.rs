use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn unsigned_shr_is_logical() {
    // int f(){ unsigned int x; x = -2; return x >> 1; }
    let src = r#"
        int f(){ unsigned int x; x = -2; return x >> 1; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");
    assert!(
        ir.contains("lshr"),
        "IR should use logical shift right (lshr) for unsigned >>:\n{}",
        ir
    );
}

#[test]
fn unsigned_div_mod_use_udiv_urem() {
    // int f(){ unsigned int a = 7; unsigned int b = 3; return a / b + a % b; }
    let src = r#"
        int f(){ unsigned int a = 7; unsigned int b = 3; return a / b + a % b; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");
    assert!(ir.contains("udiv"), "IR should use udiv for unsigned division:\n{}", ir);
    assert!(ir.contains("urem"), "IR should use urem for unsigned modulo:\n{}", ir);
}

#[test]
fn unsigned_cmp_uses_ult() {
    // int f(){ unsigned int a = 0; unsigned int b = 1; return a < b; }
    let src = r#"
        int f(){ unsigned int a = 0; unsigned int b = 1; return a < b; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");
    assert!(
        ir.contains("icmp ult"),
        "IR should use unsigned comparison predicate (ult) when comparing unsigned ints:\n{}",
        ir
    );
}
