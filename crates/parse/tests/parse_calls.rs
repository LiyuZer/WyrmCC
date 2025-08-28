use parse::{ast::*, parse_translation_unit};

#[test]
fn parse_function_with_params_and_call() {
    let src = r#"
        int add(int a, int b) { return a + b; }
        int main(void) { return add(2, 3); }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");

    assert_eq!(tu.functions.len(), 2);

    // Check add(a,b)
    let addf = &tu.functions[0];
    assert_eq!(addf.name, "add");
    assert_eq!(addf.ret_type, Type::Int);
    assert_eq!(addf.params.len(), 2);
    assert_eq!(addf.params[0].name, "a");
    assert_eq!(addf.params[0].ty, Type::Int);
    assert_eq!(addf.params[1].name, "b");
    assert_eq!(addf.params[1].ty, Type::Int);

    // Check main returns call add(2,3)
    let mainf = &tu.functions[1];
    assert_eq!(mainf.name, "main");
    assert!(matches!(
        mainf.body[0],
        Stmt::Return(Expr::Call { ref callee, ref args }) if callee == "add" && args.len() == 2
    ));
}

#[test]
fn parse_simple_call_no_args() {
    let src = r#"
        int f(void) { return 1; }
        int main(void) { return f(); }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");

    assert_eq!(tu.functions.len(), 2);
    let mainf = &tu.functions[1];

    assert!(matches!(
        mainf.body[0],
        Stmt::Return(Expr::Call { ref callee, ref args }) if callee == "f" && args.is_empty()
    ));
}
