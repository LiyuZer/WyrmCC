use backend::emit_llvm_ir;
use parse::parse_translation_unit;

// Direct struct assignment should emit a memcpy of the struct size
#[test]
fn struct_assign_memcpy_direct() {
    let src = r#"
        struct S { int a; int b; };
        int main(void) {
            struct S s1; struct S s2;
            s1.a = 1; s1.b = 2;
            s2 = s1;
            return s2.a + s2.b;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect memcpy-based struct copy
    assert!(
        ir.contains("@llvm.memcpy.p0.p0.i64"),
        "expected memcpy call for struct assignment, IR:\n{}",
        ir
    );
    // For two i32 fields, total size should be 8 bytes; look for i64 8 in call
    assert!(
        ir.contains("i64 8"),
        "expected memcpy size 8 bytes for struct S, IR:\n{}",
        ir
    );
}

// Struct assignment through pointer dereference should also emit memcpy
#[test]
fn struct_assign_memcpy_through_pointer() {
    let src = r#"
        struct S { int a; int b; };
        int main(void) {
            struct S s1; struct S s2; struct S *p = &s1;
            *p = s2; // memcpy from s2 to *p
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    assert!(
        ir.contains("@llvm.memcpy.p0.p0.i64"),
        "expected memcpy call for *p = s2 assignment, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("i64 8"),
        "expected memcpy size 8 bytes for struct S, IR:\n{}",
        ir
    );
}

// Direct union assignment should emit memcpy (size equals max member size)
#[test]
fn union_assign_memcpy_direct() {
    let src = r#"
        union U { int a; int b; };
        int main(void) {
            union U u1; union U u2;
            u1.a = 3;
            u2 = u1;
            return u2.a;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    assert!(
        ir.contains("@llvm.memcpy.p0.p0.i64"),
        "expected memcpy call for union assignment, IR:\n{}",
        ir
    );
    // For union of two ints, expect 4-byte size
    assert!(
        ir.contains("i64 4"),
        "expected memcpy size 4 bytes for union U, IR:\n{}",
        ir
    );
}
