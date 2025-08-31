use parse::parse_translation_unit;
use sema::check_translation_unit;

#[test]
fn struct_assign_same_type_ok() {
    let src = r#"
        struct S { int a; int b; };
        int main(void) {
            struct S x; struct S y;
            x = y;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert!(
        check_translation_unit(&tu).is_ok(),
        "expected sema ok for struct assignment of identical type"
    );
}

#[test]
fn struct_assign_mismatch_err() {
    let src = r#"
        struct S { int a; };
        struct T { int a; };
        int main(void) {
            struct S x; struct T y;
            x = y; // mismatched aggregate types
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let err = check_translation_unit(&tu).expect_err("expected sema error for struct assignment mismatch");
    let s = err.to_string();
    assert!(s.contains("incompatible") || s.contains("type"));
}

#[test]
fn union_assign_same_type_ok() {
    let src = r#"
        union U { int i; int *p; };
        int main(void) {
            union U u; union U v;
            u = v;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert!(
        check_translation_unit(&tu).is_ok(),
        "expected sema ok for union assignment of identical type"
    );
}

#[test]
fn union_struct_cross_err() {
    let src = r#"
        struct S { int a; };
        union U { int i; int *p; };
        int main(void) {
            struct S s; union U u;
            s = u; // cross-kind aggregate assignment
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let err = check_translation_unit(&tu).expect_err("expected sema error for struct=union assignment");
    let s = err.to_string();
    assert!(s.contains("incompatible") || s.contains("type"));
}

#[test]
fn aggregate_incomplete_err() {
    let src = r#"
        extern struct S s; // incomplete type in this TU
        int main(void) {
            struct S *p;
            *p = s; // assignment involving incomplete struct S
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let err = check_translation_unit(&tu).expect_err("expected sema error for assignment with incomplete aggregate");
    let s = err.to_string();
    assert!(s.contains("incomplete") || s.contains("incompatible") || s.contains("type"));
}
