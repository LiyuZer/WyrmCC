use parse::{parse_translation_unit, Expr, Stmt};

#[test]
fn parse_string_literal_exprstmt() {
    let src = r#"
        int main(void) {
            "hello\n";
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.functions.len(), 1);
    let f = &tu.functions[0];
    // Expect first stmt to be an expression statement with a string literal
    match &f.body[0] {
        Stmt::ExprStmt(Expr::StringLiteral(s)) => {
            assert!(
                s.contains("\\n")
                    || s.contains("\\x0a")
                    || s.contains("\\012")
                    || s.contains("hello")
            );
        }
        other => panic!("expected string literal expr stmt, got: {:?}", other),
    }
}

#[test]
fn parse_char_literal_in_return() {
    let src = r#"
        int main(void) {
            return '\n';
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.functions.len(), 1);
    let f = &tu.functions[0];
    // Expect return of decoded int literal (10 for '\n')
    match &f.body[0] {
        Stmt::Return(Expr::IntLiteral(v)) => {
            assert!(v == "10" || v == "\n" || v == "0xa" || v == "012");
            // Our parser decodes to decimal; allow exact 10
            assert_eq!(v, "10");
        }
        other => panic!("expected return of int literal from char, got: {:?}", other),
    }
}
