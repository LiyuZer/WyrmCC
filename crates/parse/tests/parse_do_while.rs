use parse::parse_translation_unit;
use parse::ast::{Expr, Stmt};

#[test]
fn parse_do_while_single_stmt() {
    let src = r#"
        int main(void) {
            do return 1; while(0);
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.functions.len(), 1);
    let f = &tu.functions[0];
    assert_eq!(f.body.len(), 1);
    match &f.body[0] {
        Stmt::DoWhile { body, cond } => {
            assert_eq!(body.len(), 1, "single-statement body should be wrapped");
            assert!(matches!(body[0], Stmt::Return(Expr::IntLiteral(ref s)) if s == "1"));
            assert!(matches!(cond, Expr::IntLiteral(ref s) if s == "0"));
        }
        other => panic!("expected do-while, got {:?}", other),
    }
}

#[test]
fn parse_do_while_block_body() {
    let src = r#"
        int main(void) {
            do { return 1; } while (0);
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];
    assert_eq!(f.body.len(), 1);
    match &f.body[0] {
        Stmt::DoWhile { body, cond } => {
            assert_eq!(body.len(), 1);
            assert!(matches!(body[0], Stmt::Return(Expr::IntLiteral(ref s)) if s == "1"));
            assert!(matches!(cond, Expr::IntLiteral(ref s) if s == "0"));
        }
        other => panic!("expected do-while with block body, got {:?}", other),
    }
}

#[test]
fn parse_do_while_nested_break_continue() {
    let src = r#"
        int main(void) {
            do { break; } while (1);
            do { continue; } while (0);
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];
    assert_eq!(f.body.len(), 3, "expected two do-while loops and a return");

    match &f.body[0] {
        Stmt::DoWhile { body, cond } => {
            assert_eq!(body.len(), 1);
            assert!(matches!(body[0], Stmt::Break));
            assert!(matches!(cond, Expr::IntLiteral(ref s) if s == "1"));
        }
        other => panic!("expected first do-while with break, got {:?}", other),
    }

    match &f.body[1] {
        Stmt::DoWhile { body, cond } => {
            assert_eq!(body.len(), 1);
            assert!(matches!(body[0], Stmt::Continue));
            assert!(matches!(cond, Expr::IntLiteral(ref s) if s == "0"));
        }
        other => panic!("expected second do-while with continue, got {:?}", other),
    }

    assert!(matches!(f.body[2], Stmt::Return(Expr::IntLiteral(ref s)) if s == "0"));
}
