use parse::parse_translation_unit;
use sema::check_translation_unit;

#[test]
fn sema_global_int_const_ok() {
    let src = r#"
        int g = 42;
        int main(void) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert!(
        check_translation_unit(&tu).is_ok(),
        "expected sema ok for const-int global init"
    );
}

#[test]
fn sema_global_nonconst_init_err() {
    let src = r#"
        int x = 7;
        int g = x; // non-constant initializer
        int main(void) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert!(
        check_translation_unit(&tu).is_err(),
        "expected sema error for non-const global init"
    );
}

#[test]
fn sema_extern_then_def_ok() {
    let src = r#"
        extern int g;
        int g = 1;
        int main(void) { return g; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert!(
        check_translation_unit(&tu).is_ok(),
        "extern then definition should be ok"
    );
}

#[test]
fn sema_duplicate_definition_err() {
    let src = r#"
        int g = 1;
        int g = 2; // duplicate definition
        int main(void) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert!(
        check_translation_unit(&tu).is_err(),
        "expected sema error for duplicate global definition"
    );
}

#[test]
fn sema_global_ptr_string_ok() {
    let src = r#"
        int *p = (int*)"hi";
        int main(void) { return p != 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert!(
        check_translation_unit(&tu).is_ok(),
        "pointer-to-string literal initializer should be ok"
    );
}
