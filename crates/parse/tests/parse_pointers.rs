use parse::{ast::*, parse_translation_unit};

#[test]
fn parse_pointer_decl_addr_deref_assign() {
    let src = r#"
        int main(void) {
            int x;
            int *p;
            p = &x;
            *p = 5;
            return x;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");

    assert_eq!(tu.functions.len(), 1);
    let f = &tu.functions[0];
    assert_eq!(f.name, "main");

    // int x;
    match &f.body[0] {
        Stmt::Decl { name, ty, init, .. } => {
            assert_eq!(name, "x");
            assert!(matches!(ty, Type::Int));
            assert!(init.is_none());
        }
        other => panic!("expected decl x, got {:?}", other),
    }

    // int *p;
    match &f.body[1] {
        Stmt::Decl { name, ty, init, .. } => {
            assert_eq!(name, "p");
            match ty {
                Type::Pointer(inner) => assert!(matches!(&**inner, Type::Int)),
                other => panic!("expected pointer to int, got {:?}", other),
            }
            assert!(init.is_none());
        }
        other => panic!("expected decl p, got {:?}", other),
    }

    // p = &x;
    match &f.body[2] {
        Stmt::ExprStmt(Expr::Assign { name, value }) => {
            assert_eq!(name, "p");
            match &**value {
                Expr::Unary {
                    op: UnaryOp::AddrOf,
                    expr,
                } => {
                    assert!(matches!(&**expr, Expr::Ident(s) if s == "x"));
                }
                other => panic!("expected &x, got {:?}", other),
            }
        }
        other => panic!("expected assign p=&x, got {:?}", other),
    }

    // *p = 5;
    match &f.body[3] {
        Stmt::ExprStmt(Expr::AssignDeref { ptr, value }) => {
            assert!(matches!(&**ptr, Expr::Ident(s) if s == "p"));
            assert!(matches!(&**value, Expr::IntLiteral(s) if s == "5"));
        }
        other => panic!("expected *p=5, got {:?}", other),
    }

    // return x;
    assert!(matches!(&f.body[4], Stmt::Return(Expr::Ident(s)) if s == "x"));
}

#[test]
fn parse_multi_level_pointer_types() {
    let src = r#"
        int main(void) {
            int *p;
            int **pp;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];

    match &f.body[0] {
        Stmt::Decl { name, ty, .. } => {
            assert_eq!(name, "p");
            match ty {
                Type::Pointer(inner) => assert!(matches!(&**inner, Type::Int)),
                other => panic!("expected pointer to int, got {:?}", other),
            }
        }
        other => panic!("expected decl p, got {:?}", other),
    }

    match &f.body[1] {
        Stmt::Decl { name, ty, .. } => {
            assert_eq!(name, "pp");
            match ty {
                Type::Pointer(inner1) => match &**inner1 {
                    Type::Pointer(inner2) => assert!(matches!(&**inner2, Type::Int)),
                    other => panic!("expected pointer to pointer, got {:?}", other),
                },
                other => panic!("expected pointer type, got {:?}", other),
            }
        }
        other => panic!("expected decl pp, got {:?}", other),
    }

    assert!(matches!(&f.body[2], Stmt::Return(Expr::IntLiteral(s)) if s == "0"));
}
