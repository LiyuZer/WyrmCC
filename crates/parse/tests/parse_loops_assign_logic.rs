use parse::{ast::*, parse_translation_unit};

#[test]
fn parse_assignment_basic() {
    let src = r#"
        int main(void) {
            int x;
            x = 5;
            return x;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.functions.len(), 1);
    let f = &tu.functions[0];
    assert_eq!(f.name, "main");
    assert_eq!(f.body.len(), 3);

    assert!(matches!(f.body[0], Stmt::Decl { ref name, ty: Type::Int, init: None, .. } if name == "x"));
    assert!(matches!(f.body[1], Stmt::ExprStmt(Expr::Assign { ref name, ref value }) if name == "x" && matches!(&**value, Expr::IntLiteral(ref s) if s == "5")));
    assert!(matches!(f.body[2], Stmt::Return(Expr::Ident(ref s)) if s == "x"));
}

#[test]
fn parse_logical_not() {
    let src = r#"
        int main(void) {
            return !0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];
    assert!(matches!(
        f.body[0],
        Stmt::Return(Expr::Unary { op: UnaryOp::LogicalNot, .. })
    ));
}

#[test]
fn parse_logical_and_or() {
    // AND
    let src1 = r#"
        int main(void) { return 0 && 1; }
    "#;
    let tu1 = parse_translation_unit(src1).expect("parse ok");
    let f1 = &tu1.functions[0];
    assert!(matches!(
        f1.body[0],
        Stmt::Return(Expr::Binary { op: BinaryOp::LAnd, .. })
    ));

    // OR
    let src2 = r#"
        int main(void) { return 1 || 0; }
    "#;
    let tu2 = parse_translation_unit(src2).expect("parse ok");
    let f2 = &tu2.functions[0];
    assert!(matches!(
        f2.body[0],
        Stmt::Return(Expr::Binary { op: BinaryOp::LOr, .. })
    ));
}

#[test]
fn parse_for_empty_sections() {
    let src = r#"
        int main(void) {
            for(;;) return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];
    assert!(matches!(f.body[0], Stmt::For { .. }));
    if let Stmt::For { ref init, ref cond, ref post, ref body } = f.body[0] {
        assert!(init.is_none());
        assert!(cond.is_none());
        assert!(post.is_none());
        assert_eq!(body.len(), 1);
        assert!(matches!(body[0], Stmt::Return(Expr::IntLiteral(ref s)) if s == "0"));
    } else {
        panic!("expected For stmt");
    }
}

#[test]
fn parse_for_with_init_cond_post() {
    let src = r#"
        int main(void) {
            int i;
            for(i=0; i<3; i=i+1) return i;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];
    assert!(matches!(f.body[0], Stmt::Decl { ref name, ty: Type::Int, .. } if name == "i"));
    assert!(matches!(f.body[1], Stmt::For { .. }));
    if let Stmt::For { ref init, ref cond, ref post, ref body } = f.body[1] {
        // init: i = 0
        match init {
            Some(Expr::Assign { name, value }) => {
                assert_eq!(name, "i");
                assert!(matches!(**value, Expr::IntLiteral(ref s) if s == "0"));
            }
            other => panic!("unexpected init: {:?}", other),
        }
        // cond: i < 3
        match cond {
            Some(Expr::Binary { op: BinaryOp::Lt, lhs, rhs }) => {
                assert!(matches!(**lhs, Expr::Ident(ref s) if s == "i"));
                assert!(matches!(**rhs, Expr::IntLiteral(ref s) if s == "3"));
            }
            other => panic!("unexpected cond: {:?}", other),
        }
        // post: i = i + 1
        match post {
            Some(Expr::Assign { name, value }) => {
                assert_eq!(name, "i");
                match &**value {
                    Expr::Binary { op: BinaryOp::Plus, lhs, rhs } => {
                        assert!(matches!(**lhs, Expr::Ident(ref s) if s == "i"));
                        assert!(matches!(**rhs, Expr::IntLiteral(ref s) if s == "1"));
                    }
                    other => panic!("unexpected post value: {:?}", other),
                }
            }
            other => panic!("unexpected post: {:?}", other),
        }
        // body: return i;
        assert_eq!(body.len(), 1);
        assert!(matches!(body[0], Stmt::Return(Expr::Ident(ref s)) if s == "i"));
    }
}