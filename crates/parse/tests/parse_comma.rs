use parse::{ast::*, parse_translation_unit};

#[test]
fn parse_return_parens_comma() {
    let src = r#"
        int main(void) {
            return (1, 2);
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.functions.len(), 1);
    let f = &tu.functions[0];
    assert_eq!(f.name, "main");
    assert_eq!(f.body.len(), 1);
    match &f.body[0] {
        Stmt::Return(Expr::Comma { lhs, rhs }) => {
            assert!(matches!(&**lhs, Expr::IntLiteral(ref s) if s == "1"));
            assert!(matches!(&**rhs, Expr::IntLiteral(ref s) if s == "2"));
        }
        other => panic!("unexpected stmt: {:?}", other),
    }
}

#[test]
fn parse_for_init_and_post_with_commas() {
    let src = r#"
        int main(void) {
            int i; int j;
            for(i=0, j=0; i<3; i++, j++) { }
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];
    assert_eq!(f.name, "main");
    // Expect: Decl i; Decl j; For { init: Comma( Assign(i,0), Assign(j,0) ), post: Comma( IncDec(i), IncDec(j) ) }
    assert!(matches!(f.body[0], Stmt::Decl { ref name, ty: Type::Int, .. } if name == "i"));
    assert!(matches!(f.body[1], Stmt::Decl { ref name, ty: Type::Int, .. } if name == "j"));
    match &f.body[2] {
        Stmt::For {
            init,
            cond,
            post,
            body,
        } => {
            // init
            match init {
                Some(Expr::Comma { lhs, rhs }) => match (&**lhs, &**rhs) {
                    (
                        Expr::Assign {
                            name: n1,
                            value: v1,
                        },
                        Expr::Assign {
                            name: n2,
                            value: v2,
                        },
                    ) => {
                        assert_eq!(n1, "i");
                        assert!(matches!(&**v1, Expr::IntLiteral(ref s) if s == "0"));
                        assert_eq!(n2, "j");
                        assert!(matches!(&**v2, Expr::IntLiteral(ref s) if s == "0"));
                    }
                    other => panic!("unexpected init comma pair: {:?}", other),
                },
                other => panic!("unexpected init: {:?}", other),
            }
            // cond
            match cond {
                Some(Expr::Binary {
                    op: BinaryOp::Lt,
                    lhs,
                    rhs,
                }) => {
                    assert!(matches!(&**lhs, Expr::Ident(ref s) if s == "i"));
                    assert!(matches!(&**rhs, Expr::IntLiteral(ref s) if s == "3"));
                }
                other => panic!("unexpected cond: {:?}", other),
            }
            // post
            match post {
                Some(Expr::Comma { lhs, rhs }) => {
                    // post is i++, j++ (as postfix)
                    match (&**lhs, &**rhs) {
                        (
                            Expr::IncDec {
                                pre: false,
                                inc: true,
                                target: t1,
                            },
                            Expr::IncDec {
                                pre: false,
                                inc: true,
                                target: t2,
                            },
                        ) => {
                            assert!(matches!(&**t1, Expr::Ident(ref s) if s == "i"));
                            assert!(matches!(&**t2, Expr::Ident(ref s) if s == "j"));
                        }
                        other => panic!("unexpected post comma pair: {:?}", other),
                    }
                }
                other => panic!("unexpected post: {:?}", other),
            }
            // body is empty block
            assert!(body.is_empty());
        }
        other => panic!("expected for-stmt, got: {:?}", other),
    }
}

#[test]
fn call_args_not_folded_by_comma() {
    let src = r#"
        int foo(int a, int b) { return a + b; }
        int main(void) { return foo(1, 2); }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.functions.len(), 2);
    let main_fn = &tu.functions[1];
    match &main_fn.body[0] {
        Stmt::Return(Expr::Call { callee, args }) => {
            assert_eq!(callee, "foo");
            assert_eq!(args.len(), 2);
            assert!(matches!(args[0], Expr::IntLiteral(ref s) if s == "1"));
            assert!(matches!(args[1], Expr::IntLiteral(ref s) if s == "2"));
        }
        other => panic!("unexpected return expr: {:?}", other),
    }
}
