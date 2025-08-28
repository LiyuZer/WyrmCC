use parse::parse_translation_unit;
use parse::ast::{Expr, Stmt, Type, UnaryOp, BinaryOp};

fn find_return_expr(stmts: &[Stmt]) -> Option<&Expr> {
    for s in stmts {
        match s {
            Stmt::Return(e) => return Some(e),
            Stmt::Block(b) => {
                if let Some(e) = find_return_expr(b) { return Some(e); }
            }
            _ => {}
        }
    }
    None
}

#[test]
fn parse_int_cast_of_ident() {
    let src = r#"
        int main(void) {
            int x;
            return (int)x;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.functions.len(), 1);
    let f = &tu.functions[0];
    let ret_e = find_return_expr(&f.body).expect("has return");
    match ret_e {
        Expr::Cast { ty, expr } => {
            assert_eq!(ty, &Type::Int);
            assert!(matches!(&**expr, Expr::Ident(name) if name == "x"));
        }
        other => panic!("expected Cast(Int, Ident x), got {:?}", other),
    }
}

#[test]
fn parse_pointer_cast_of_addrof() {
    let src = r#"
        int main(void) {
            int x; int *p; p = (int*)&x; return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];
    // Find the assignment to p
    let mut saw_assign = false;
    for s in &f.body {
        if let Stmt::ExprStmt(e) = s {
            if let Expr::Assign { name, value } = e {
                if name == "p" {
                    if let Expr::Cast { ty, expr } = &**value {
                        assert!(matches!(ty, Type::Pointer(inner) if **inner == Type::Int));
                        match &**expr {
                            Expr::Unary { op: UnaryOp::AddrOf, expr } => {
                                assert!(matches!(&**expr, Expr::Ident(n) if n == "x"));
                            }
                            other => panic!("expected AddrOf(Ident x), got {:?}", other),
                        }
                        saw_assign = true;
                        break;
                    } else {
                        panic!("expected cast on RHS of p assignment");
                    }
                }
            }
        }
    }
    assert!(saw_assign, "did not find assignment to p with cast");
}

#[test]
fn parse_nested_cast_of_binary() {
    let src = r#"
        int main(void) {
            return (int)(1 + 2);
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];
    let ret_e = find_return_expr(&f.body).expect("has return");
    match ret_e {
        Expr::Cast { ty, expr } => {
            assert_eq!(ty, &Type::Int);
            match &**expr {
                Expr::Binary { op: BinaryOp::Plus, lhs, rhs } => {
                    assert!(matches!(&**lhs, Expr::IntLiteral(s) if s == "1"));
                    assert!(matches!(&**rhs, Expr::IntLiteral(s) if s == "2"));
                }
                other => panic!("expected Binary Plus(1,2), got {:?}", other),
            }
        }
        other => panic!("expected Cast(Int, (1+2)), got {:?}", other),
    }
}

#[test]
fn cast_precedence_in_addition() {
    let src = r#"
        int main(void) {
            return (int)1 + 2;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];
    let ret_e = find_return_expr(&f.body).expect("has return");
    match ret_e {
        Expr::Binary { op: BinaryOp::Plus, lhs, rhs } => {
            match &**lhs {
                Expr::Cast { ty, expr } => {
                    assert_eq!(ty, &Type::Int);
                    assert!(matches!(&**expr, Expr::IntLiteral(s) if s == "1"));
                }
                other => panic!("expected Cast(Int,1) on LHS, got {:?}", other),
            }
            assert!(matches!(&**rhs, Expr::IntLiteral(s) if s == "2"));
        }
        other => panic!("expected Binary Plus with cast on LHS, got {:?}", other),
    }
}
