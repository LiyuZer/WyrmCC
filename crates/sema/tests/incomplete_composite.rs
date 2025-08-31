use sema::check_translation_unit;

// Incomplete struct/union object declarations and sizeof completeness

#[test]
fn struct_incomplete_object_err() {
    let src = r#"
        struct S;
        int main(void) {
            struct S x; // object of incomplete type
            return 0;
        }
    "#;
    let tu = parse::parse_translation_unit(src).expect("parse ok");
    let err = check_translation_unit(&tu).expect_err("should error: object of incomplete struct type");
    let s = err.to_string();
    assert!(s.contains("incomplete") || s.contains("object"));
}

#[test]
fn struct_incomplete_pointer_ok() {
    let src = r#"
        struct S;
        int main(void) {
            struct S *p; // pointer to incomplete type is OK
            return 0;
        }
    "#;
    let tu = parse::parse_translation_unit(src).expect("parse ok");
    check_translation_unit(&tu).expect("pointer to incomplete struct is OK");
}

#[test]
fn sizeof_incomplete_struct_err() {
    let src = r#"
        struct S;
        int main(void) {
            return sizeof(struct S); // sizeof incomplete type
        }
    "#;
    let tu = parse::parse_translation_unit(src).expect("parse ok");
    let err = check_translation_unit(&tu).expect_err("should error: sizeof incomplete struct");
    let s = err.to_string();
    assert!(s.contains("incomplete") || s.contains("sizeof"));
}

#[test]
fn sizeof_incomplete_array_elem_err() {
    // Use cast to pointer-to-array abstract declarator to form sizeof of an array of incomplete elements,
    // then deref to compute the array object size: sizeof(*( (struct S (*)[3])0 )).
    let src = r#"
        struct S;
        int main(void) {
            return sizeof(*( (struct S (*)[3])0 )); // sizeof array with incomplete element type
        }
    "#;
    let tu = parse::parse_translation_unit(src).expect("parse ok");
    let err = check_translation_unit(&tu).expect_err("should error: sizeof array with incomplete element");
    let s = err.to_string();
    assert!(s.contains("incomplete") || s.contains("sizeof"));
}

#[test]
fn extern_incomplete_ok_then_pointer_use() {
    let src = r#"
        struct S;
        extern struct S g; // extern of incomplete is OK
        int main(void) {
            struct S *p;
            (void)p;
            return 0;
        }
    "#;
    let tu = parse::parse_translation_unit(src).expect("parse ok");
    check_translation_unit(&tu).expect("extern incomplete and pointer use OK");
}

// Composite type compatibility for global arrays (v1: single dimension)

#[test]
fn array_unsized_then_sized_ok() {
    let src = r#"
        int a[];
        int a[3];
        int main(void) { return 0; }
    "#;
    let tu = parse::parse_translation_unit(src).expect("parse ok");
    check_translation_unit(&tu).expect("unsized then sized array should be OK");
}

#[test]
fn array_sized_then_unsized_ok() {
    let src = r#"
        int a[3];
        int a[];
        int main(void) { return 0; }
    "#;
    let tu = parse::parse_translation_unit(src).expect("parse ok");
    check_translation_unit(&tu).expect("sized then unsized array should be OK");
}

#[test]
fn array_conflicting_sizes_err() {
    let src = r#"
        int a[3];
        int a[4];
        int main(void) { return 0; }
    "#;
    let tu = parse::parse_translation_unit(src).expect("parse ok");
    let err = check_translation_unit(&tu).expect_err("should error: conflicting array sizes");
    let s = err.to_string();
    assert!(s.contains("array") || s.contains("size") || s.contains("conflict"));
}

#[test]
fn extern_array_unsized_then_def_sized_ok() {
    let src = r#"
        extern int a[];
        int a[5];
        int main(void) { return 0; }
    "#;
    let tu = parse::parse_translation_unit(src).expect("parse ok");
    check_translation_unit(&tu).expect("extern unsized then sized definition OK");
}

#[test]
fn union_incomplete_object_err() {
    let src = r#"
        union U;
        int main(void) {
            union U u; // object of incomplete union type
            return 0;
        }
    "#;
    let tu = parse::parse_translation_unit(src).expect("parse ok");
    let err = check_translation_unit(&tu).expect_err("should error: object of incomplete union type");
    let s = err.to_string();
    assert!(s.contains("incomplete") || s.contains("object"));
}
