use backend::emit_llvm_ir;
use parse::parse_translation_unit;

// Pointer-to-struct array decay: p[2].y where p = a (a is struct array)
#[test]
fn ptr_to_struct_index_member() {
    let src = r#"
        struct P { int x; int y; };
        int main(void) {
            struct P a[3];
            struct P *p = a;
            p[2].y = 9;
            return p[2].y;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect byte-wise GEP used to compute element and field addresses
    assert!(
        ir.contains("getelementptr inbounds i8"),
        "expected i8 GEP for pointer-to-struct indexing, IR:\n{}",
        ir
    );
    // Store and later return
    assert!(
        ir.contains("store i32 9"),
        "expected store of 9 to p[2].y, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("load i32, ptr"),
        "expected load from computed member pointer, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("ret i32"),
        "expected a return instruction, IR:\n{}",
        ir
    );
}

// Nested arrays of structs: a[1].b.z chain
#[test]
fn nested_array_struct_member_chain() {
    let src = r#"
        struct B { int z; };
        struct A { int x; struct B b; };
        int main(void) {
            struct A a[2];
            a[1].b.z = 5;
            return a[1].b.z;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // We expect nested i8 GEPs: one for array element, another for member offsets
    assert!(
        ir.contains("getelementptr inbounds i8"),
        "expected i8 GEPs for nested member chain, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("store i32 5"),
        "expected store of 5 to a[1].b.z, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("load i32, ptr"),
        "expected load from computed member pointer, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("ret i32"),
        "expected return instruction, IR:\n{}",
        ir
    );
}

// Arrays of unions: u[1].i access should use element scaling and offset 0 within union
#[test]
fn array_of_unions_element_member() {
    let src = r#"
        union U { int i; int *p; };
        int main(void) {
            union U u[2];
            u[1].i = 3;
            return u[1].i;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect i8 GEPs and an explicit offset 0 for the union member access
    assert!(
        ir.contains("getelementptr inbounds i8"),
        "expected i8 GEP for array-of-union element, IR:\n{}",
        ir
    );
    assert!(
        ir.contains(", i64 0") || ir.matches(", i64 ").count() > 1,
        "expected a GEP including offset 0 for union member, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("store i32 3"),
        "expected store of 3 to u[1].i, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("ret i32"),
        "expected return instruction, IR:\n{}",
        ir
    );
}
