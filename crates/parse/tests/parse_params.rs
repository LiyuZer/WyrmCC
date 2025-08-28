use parse::{parse_translation_unit, Type};

#[test]
fn parse_two_params() {
    let src = r#"
        int add(int a, int b) {
            return a + b;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.functions.len(), 1);
    let f = &tu.functions[0];
    assert_eq!(f.name, "add");
    assert_eq!(f.ret_type, Type::Int);
    assert_eq!(f.params.len(), 2);
    assert_eq!(f.params[0].name, "a");
    assert_eq!(f.params[0].ty, Type::Int);
    assert_eq!(f.params[1].name, "b");
    assert_eq!(f.params[1].ty, Type::Int);
}

#[test]
fn parse_empty_param_list() {
    let src = r#"
        int f() { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.functions.len(), 1);
    let f = &tu.functions[0];
    assert_eq!(f.name, "f");
    assert_eq!(f.params.len(), 0);
}

#[test]
fn parse_void_param_list() {
    let src = r#"
        int f(void) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.functions.len(), 1);
    let f = &tu.functions[0];
    assert_eq!(f.name, "f");
    assert_eq!(f.params.len(), 0);
}

#[test]
fn parse_pointer_params() {
    let src = r#"
        int f(int *p, void *q) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.functions.len(), 1);
    let f = &tu.functions[0];
    assert_eq!(f.name, "f");
    assert_eq!(f.params.len(), 2);
    assert_eq!(f.params[0].name, "p");
    assert_eq!(f.params[0].ty, Type::Pointer(Box::new(Type::Int)));
    assert_eq!(f.params[1].name, "q");
    assert_eq!(f.params[1].ty, Type::Pointer(Box::new(Type::Void)));
}
