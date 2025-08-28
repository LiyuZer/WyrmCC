use backend::emit_llvm_ir;
use parse::parse_translation_unit;

// Struct member via dot: s.a = 5; return s.a;
#[test]
fn struct_dot_load_store() {
    let src = r#"
        struct S { int a; int b; };
        int main(void) {
            struct S s;
            s.a = 5;
            return s.a;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Should allocate some bytes for struct storage
    assert!(ir.contains("alloca i8"), "expected byte allocation for struct storage, IR:\n{}", ir);
    // Access field a at offset 0 via i8 GEP
    assert!(ir.contains("getelementptr inbounds i8") && ir.contains(", i64 0"),
        "expected GEP to field a at byte offset 0, IR:\n{}", ir);
    // Store 5 into the field and later load it
    assert!(ir.contains("store i32 5"), "expected store of 5 to struct field, IR:\n{}", ir);
    assert!(ir.contains("load i32"), "expected load from struct field, IR:\n{}", ir);
}

// Struct member via arrow: q->a = 2; return s.a; (q = &s)
#[test]
fn struct_arrow_store_then_read_from_base() {
    let src = r#"
        struct S { int a; };
        int main(void) {
            struct S s;
            struct S *q = &s;
            q->a = 2;
            return s.a;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect pointer member access via i8 GEP and store 2
    assert!(ir.contains("getelementptr inbounds i8"), "expected i8 GEP for member access, IR:\n{}", ir);
    assert!(ir.contains("store i32 2"), "expected store 2 to q->a, IR:\n{}", ir);
    // And later load and return value from s.a
    assert!(ir.contains("load i32"), "expected load from s.a, IR:\n{}", ir);
}

// Union member via dot: u.a = 7; return u.a; (byte offset 0)
#[test]
fn union_dot_access_basic() {
    let src = r#"
        union U { int a; int *p; };
        int main(void) {
            union U u;
            u.a = 7;
            return u.a;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Union members share offset 0
    assert!(ir.contains("getelementptr inbounds i8") && ir.contains(", i64 0"),
        "expected GEP to union member at offset 0, IR:\n{}", ir);
    assert!(ir.contains("store i32 7"), "expected store 7 to union field, IR:\n{}", ir);
    assert!(ir.contains("load i32"), "expected load from union field, IR:\n{}", ir);
}
