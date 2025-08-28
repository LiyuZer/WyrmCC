use parse::parse_translation_unit;

#[test]
fn parse_struct_def_and_forward() {
    // int main(void){ struct S; struct S { int a; int b; }; return 0; }
    let src = r#"
        int main(void) {
            struct S;
            struct S { int a; int b; };
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src);
    assert!(tu.is_ok(), "expected parse ok, got {:?}", tu);
}

#[test]
fn parse_union_and_enum() {
    // int main(void){ union U { int a; }; enum E { A, B, C }; return 0; }
    let src = r#"
        int main(void) {
            union U { int a; };
            enum E { A, B, C };
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src);
    assert!(tu.is_ok(), "expected parse ok, got {:?}", tu);
}

#[test]
fn parse_decl_with_storage_and_qualifiers() {
    // int main(void){ extern int gx; const int *p; volatile int x; return 0; }
    // Note: extern inside function is a declaration (no definition) — parser should accept it.
    let src = r#"
        int main(void) {
            extern int gx;
            const int *p;
            volatile int x;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src);
    assert!(tu.is_ok(), "expected parse ok, got {:?}", tu);
}

#[test]
fn parse_sizeof_type_with_struct_and_union() {
    // int main(void){ struct S { int a; }; union U { int a; }; return sizeof(struct S) + sizeof(union U); }
    let src = r#"
        int main(void) {
            struct S { int a; };
            union U { int a; };
            return sizeof(struct S) + sizeof(union U);
        }
    "#;
    let tu = parse_translation_unit(src);
    assert!(tu.is_ok(), "expected parse ok, got {:?}", tu);
}
