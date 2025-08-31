use parse::*;

fn tu(src: &str) -> TranslationUnit {
    parse_translation_unit(src).expect("parse ok")
}

#[test]
fn parses_empty_and_nested_blocks() {
    let src = r#"int main() { { } { { return 1; } } return 0; }"#;
    let tu = tu(src);
    assert_eq!(tu.functions.len(), 1);
    let f = &tu.functions[0];
    // Expect: Block([]), Block([Block([Return(1)])]), Return(0)
    assert!(matches!(f.body[0], Stmt::Block(ref b) if b.is_empty()));
    match &f.body[1] {
        Stmt::Block(b1) => {
            assert_eq!(b1.len(), 1);
            match &b1[0] {
                Stmt::Block(b2) => {
                    assert_eq!(b2.len(), 1);
                    assert!(matches!(b2[0], Stmt::Return(Expr::IntLiteral(ref s)) if s == "1"));
                }
                _ => panic!("expected inner block"),
            }
        }
        _ => panic!("expected block"),
    }
    assert!(matches!(f.body[2], Stmt::Return(Expr::IntLiteral(ref s)) if s == "0"));
}

#[test]
fn parses_if_no_else_then_stmt() {
    let src = r#"int main() { if (1) return 1; return 0; }"#;
    let tu = tu(src);
    let f = &tu.functions[0];
    match &f.body[0] {
        Stmt::If {
            cond,
            then_branch,
            else_branch,
        } => {
            assert!(matches!(cond, Expr::IntLiteral(ref s) if s == "1"));
            assert_eq!(then_branch.len(), 1);
            assert!(matches!(then_branch[0], Stmt::Return(Expr::IntLiteral(ref s)) if s == "1"));
            assert!(else_branch.is_none());
        }
        _ => panic!("expected if"),
    }
    assert!(matches!(f.body[1], Stmt::Return(Expr::IntLiteral(ref s)) if s == "0"));
}

#[test]
fn parses_if_else_with_blocks() {
    let src = r#"int main() { if (0) { return 1; } else { return 2; } }"#;
    let tu = tu(src);
    let f = &tu.functions[0];
    assert_eq!(f.body.len(), 1);
    match &f.body[0] {
        Stmt::If {
            cond,
            then_branch,
            else_branch,
        } => {
            assert!(matches!(cond, Expr::IntLiteral(ref s) if s == "0"));
            assert_eq!(then_branch.len(), 1);
            assert!(matches!(then_branch[0], Stmt::Return(Expr::IntLiteral(ref s)) if s == "1"));
            let eb = else_branch.as_ref().expect("else present");
            assert_eq!(eb.len(), 1);
            assert!(matches!(eb[0], Stmt::Return(Expr::IntLiteral(ref s)) if s == "2"));
        }
        _ => panic!("expected if/else"),
    }
}

#[test]
fn parses_while_with_block_break_and_stmt_continue() {
    let src = r#"int main() { int i; while (1) { break; } while (0) continue; return 0; }"#;
    let tu = tu(src);
    let f = &tu.functions[0];
    // Expect: Decl i; While(1, Block[Break]); While(0, [Continue]); Return(0)
    assert!(matches!(f.body[0], Stmt::Decl { ref name, .. } if name == "i"));
    match &f.body[1] {
        Stmt::While { cond, body } => {
            assert!(matches!(cond, Expr::IntLiteral(ref s) if s == "1"));
            assert_eq!(body.len(), 1);
            assert!(matches!(body[0], Stmt::Break));
        }
        _ => panic!("expected first while"),
    }
    match &f.body[2] {
        Stmt::While { cond, body } => {
            assert!(matches!(cond, Expr::IntLiteral(ref s) if s == "0"));
            assert_eq!(body.len(), 1);
            assert!(matches!(body[0], Stmt::Continue));
        }
        _ => panic!("expected second while"),
    }
    assert!(matches!(f.body[3], Stmt::Return(Expr::IntLiteral(ref s)) if s == "0"));
}

#[test]
fn parses_while_with_single_stmt_body() {
    let src = r#"int main() { while (1) return 1; }"#;
    let tu = tu(src);
    let f = &tu.functions[0];
    assert_eq!(f.body.len(), 1);
    match &f.body[0] {
        Stmt::While { cond, body } => {
            assert!(matches!(cond, Expr::IntLiteral(ref s) if s == "1"));
            assert_eq!(body.len(), 1);
            assert!(matches!(body[0], Stmt::Return(Expr::IntLiteral(ref s)) if s == "1"));
        }
        _ => panic!("expected while"),
    }
}

#[test]
fn else_binds_to_nearest_if() {
    // else should bind to the inner if
    let src = r#"int main() { if (1) if (0) return 1; else return 2; return 3; }"#;
    let tu = tu(src);
    let f = &tu.functions[0];
    assert!(matches!(f.body[1], Stmt::Return(Expr::IntLiteral(ref s)) if s == "3"));
    match &f.body[0] {
        Stmt::If {
            cond: outer_cond,
            then_branch,
            else_branch,
        } => {
            assert!(matches!(outer_cond, Expr::IntLiteral(ref s) if s == "1"));
            assert!(else_branch.is_none());
            assert_eq!(then_branch.len(), 1);
            match &then_branch[0] {
                Stmt::If {
                    cond: inner_cond,
                    then_branch: t2,
                    else_branch: e2,
                } => {
                    assert!(matches!(inner_cond, Expr::IntLiteral(ref s) if s == "0"));
                    assert_eq!(t2.len(), 1);
                    assert!(matches!(t2[0], Stmt::Return(Expr::IntLiteral(ref s)) if s == "1"));
                    let e2 = e2.as_ref().expect("inner else present");
                    assert_eq!(e2.len(), 1);
                    assert!(matches!(e2[0], Stmt::Return(Expr::IntLiteral(ref s)) if s == "2"));
                }
                _ => panic!("expected inner if"),
            }
        }
        _ => panic!("expected outer if"),
    }
}
