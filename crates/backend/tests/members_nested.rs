use backend::emit_llvm_ir;
use parse::parse_translation_unit;

// Nested struct via dot: s.in.a = 3; s.in.b = 4;
#[test]
fn nested_struct_dot_access() {
    let src = r#"
        struct Inner { int a; int b; };
        struct Outer { int x; struct Inner in; int y; };
        int main(void) {
            struct Outer s;
            s.in.a = 3;
            s.in.b = 4;
            return s.in.a + s.in.b;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect i8 GEPs for member access
    assert!(
        ir.contains("getelementptr inbounds i8"),
        "expected i8 GEP for nested member access, IR:\n{}",
        ir
    );
    // Expect stores of the constants
    assert!(
        ir.contains("store i32 3"),
        "expected store of 3 to s.in.a, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("store i32 4"),
        "expected store of 4 to s.in.b, IR:\n{}",
        ir
    );
}

// Nested struct via arrow: p->in.a = 5; p->in.b = 6;
#[test]
fn nested_struct_arrow_access() {
    let src = r#"
        struct Inner { int a; int b; };
        struct Outer { int x; struct Inner in; int y; };
        int main(void) {
            struct Outer s;
            struct Outer *p = &s;
            p->in.a = 5;
            p->in.b = 6;
            return s.in.a + s.in.b;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect i8 GEPs and stores through pointer member access
    assert!(
        ir.contains("getelementptr inbounds i8"),
        "expected i8 GEP for nested pointer member access, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("store i32 5"),
        "expected store 5 to p->in.a, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("store i32 6"),
        "expected store 6 to p->in.b, IR:\n{}",
        ir
    );
}

// Union inside struct overlay semantics (offset 0 for union members)
#[test]
fn union_in_struct_overlay_offsets() {
    let src = r#"
        union U { int a; int b; };
        struct W { union U u; int z; };
        int main(void) {
            struct W w;
            w.u.a = 0x01020304;
            w.z = 9;
            return w.u.b; // read from the same offset as u.a
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect union field access at byte offset 0
    assert!(
        ir.contains("getelementptr inbounds i8") && ir.contains(", i64 0"),
        "expected GEP to union member at offset 0, IR:\n{}",
        ir
    );
    // Expect separate access to z at a non-zero offset (commonly 4)
    assert!(
        ir.contains(", i64 4") || ir.matches(", i64 ").count() > 1,
        "expected non-zero offset GEP for z field, IR:\n{}",
        ir
    );
}
