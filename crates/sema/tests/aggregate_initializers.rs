use parse::parse_translation_unit;
use sema::check_translation_unit;

#[test]
fn array_too_many_initializers_err() {
    let src = r#"
        int main(void) {
            int a[2] = {1,2,3};
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let res = check_translation_unit(&tu);
    assert!(res.is_err(), "expected too many initializers error for array");
}

#[test]
fn unsized_array_from_list_ok() {
    let src = r#"
        int main(void) {
            int a[] = {1,2,3};
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let res = check_translation_unit(&tu);
    assert!(res.is_ok(), "unsized array with list should be accepted");
}

#[test]
fn char_array_string_sizes() {
    let ok_src = r#"
        int main(void) {
            char s[5] = "hi"; // needs 3 (including NUL)
            return 0;
        }
    "#;
    let tu_ok = parse_translation_unit(ok_src).expect("parse ok");
    assert!(check_translation_unit(&tu_ok).is_ok(), "char[5] = \"hi\" should be ok");

    let bad_src = r#"
        int main(void) {
            char s[2] = "hi"; // too small for NUL
            return 0;
        }
    "#;
    let tu_bad = parse_translation_unit(bad_src).expect("parse ok");
    assert!(check_translation_unit(&tu_bad).is_err(), "char[2] = \"hi\" should error");
}

#[test]
fn array_of_arrays_nested_init_ok() {
    let src = r#"
        int main(void) {
            int m[2][2] = { {1,2}, {3,4} };
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let res = check_translation_unit(&tu);
    assert!(res.is_ok(), "nested initializer for array-of-arrays should be accepted");
}

#[test]
fn struct_partial_and_too_many() {
    let ok_src = r#"
        int main(void) {
            struct S { int a; int b; };
            struct S s = {1}; // partial init ok
            return 0;
        }
    "#;
    let tu_ok = parse_translation_unit(ok_src).expect("parse ok");
    assert!(check_translation_unit(&tu_ok).is_ok(), "partial struct init should be ok");

    let bad_src = r#"
        int main(void) {
            struct S { int a; int b; };
            struct S s = {1,2,3}; // too many
            return 0;
        }
    "#;
    let tu_bad = parse_translation_unit(bad_src).expect("parse ok");
    assert!(check_translation_unit(&tu_bad).is_err(), "too many struct initializers should error");
}

#[test]
fn struct_with_array_field_nested_ok() {
    // Brace-init for array field inside struct; local scope
    let src = r#"
        int main(void) {
            struct T { int a[2]; int b; };
            struct T t = { {1,2}, 3 };
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let res = check_translation_unit(&tu);
    // May fail until implementation supports nested initializer for struct field arrays
    assert!(res.is_ok(), "nested initializer for struct field array should be accepted");
}
