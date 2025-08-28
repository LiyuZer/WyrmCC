use parse::parse_translation_unit;
use parse::ast::{Expr, Stmt, Type};

fn find_decl<'a>(stmts: &'a [Stmt], name: &str) -> Option<(&'a String, &'a Type)> {
    for s in stmts {
        match s {
            Stmt::Decl { name: n, ty, .. } if n == name => return Some((n, ty)),
            Stmt::Block(b) => if let Some(found) = find_decl(b, name) { return Some(found); },
            _ => {}
        }
    }
    None
}

fn find_return_expr<'a>(stmts: &'a [Stmt]) -> Option<&'a Expr> {
    for s in stmts {
        match s {
            Stmt::Return(e) => return Some(e),
            Stmt::Block(b) => if let Some(e) = find_return_expr(b) { return Some(e); },
            _ => {}
        }
    }
    None
}

#[test]
fn parse_decl_int_array() {
    let src = r#"
        int main(void) {
            int a[3];
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.functions.len(), 1);
    let f = &tu.functions[0];
    let (_n, ty) = find_decl(&f.body, "a").expect("found decl a");
    match ty {
        Type::Array(inner, n) => {
            assert!(matches!(&**inner, Type::Int), "inner type should be int, got {:?}", inner);
            assert_eq!(*n, 3usize);
        }
        other => panic!("expected array type, got {:?}", other),
    }
}

#[test]
fn parse_return_index_expr() {
    let src = r#"
        int main(void) {
            int a[3];
            return a[1];
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];
    let ret_e = find_return_expr(&f.body).expect("has return");
    match ret_e {
        Expr::Index { base, index } => {
            assert!(matches!(&**base, Expr::Ident(s) if s == "a"));
            assert!(matches!(&**index, Expr::IntLiteral(repr) if repr == "1"));
        }
        other => panic!("expected Index(a,1), got {:?}", other),
    }
}
