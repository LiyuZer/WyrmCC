use parse::parse_translation_unit;

#[test]
fn parse_variadic_prototype_ok() {
    let src = r#"
        int printf(const char* fmt, ...);
    "#;
    let _ = parse_translation_unit(src).expect("parse ok");
}

#[test]
fn parse_variadic_definition_ok() {
    let src = r#"
        int sum(int a, ...) { return a; }
    "#;
    let _ = parse_translation_unit(src).expect("parse ok");
}

#[test]
fn parse_variadic_invalid_no_named_param() {
    let src = r#"
        int bad(...) { return 0; }
    "#;
    assert!(
        parse_translation_unit(src).is_err(),
        "expected error for f(...)"
    );
}

#[test]
fn parse_variadic_invalid_not_last() {
    let src = r#"
        int g(int a, ..., int b) { return a; }
    "#;
    assert!(
        parse_translation_unit(src).is_err(),
        "expected error when ... is not last"
    );
}
