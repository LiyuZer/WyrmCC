use parse::{ast::*, parse_translation_unit};

#[test]
fn parse_minimal_main_return_0() {
    let src = r#"
        int main(void) {
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.functions.len(), 1);
    let f = &tu.functions[0];
    assert_eq!(f.name, "main");
    assert_eq!(f.ret_type, Type::Int);
    assert!(f.params.is_empty());
    assert!(matches!(f.body[0], Stmt::Return(Expr::IntLiteral(ref s)) if s == "0"));
}

#[test]
fn parse_decl_and_return_ident() {
    let src = r#"
        int main(void) {
            int y = 3 + 4;
            return y;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];
    assert!(matches!(f.body[0], Stmt::Decl{ ref name, .. } if name == "y"));
    assert!(matches!(f.body[1], Stmt::Return(Expr::Ident(ref s)) if s == "y"));
}
