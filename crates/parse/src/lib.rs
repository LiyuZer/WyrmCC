pub mod ast;
mod parser;

pub use ast::*;
pub use parser::parse_translation_unit;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_label_simple() {
        let src = "int main(){ L: return 0; }";
        let tu = parse_translation_unit(src).unwrap();
        assert_eq!(tu.functions.len(), 1);
        let f = &tu.functions[0];
        assert_eq!(f.name, "main");
        assert_eq!(
            f.body,
            vec![
                Stmt::Label("L".to_string()),
                Stmt::Return(Expr::IntLiteral("0".to_string())),
            ]
        );
    }

    #[test]
    fn parse_goto_to_label() {
        let src = "int main(){ goto L; L: return 0; }";
        let tu = parse_translation_unit(src).unwrap();
        assert_eq!(tu.functions.len(), 1);
        let f = &tu.functions[0];
        assert_eq!(
            f.body,
            vec![
                Stmt::Goto("L".to_string()),
                Stmt::Label("L".to_string()),
                Stmt::Return(Expr::IntLiteral("0".to_string())),
            ]
        );
    }

    #[test]
    fn parse_stacked_labels() {
        let src = "int main(){ A: B: return 1; }";
        let tu = parse_translation_unit(src).unwrap();
        assert_eq!(tu.functions.len(), 1);
        let f = &tu.functions[0];
        assert_eq!(
            f.body,
            vec![
                Stmt::Label("A".to_string()),
                Stmt::Label("B".to_string()),
                Stmt::Return(Expr::IntLiteral("1".to_string())),
            ]
        );
    }

    #[test]
    fn parse_goto_requires_semicolon() {
        // Missing semicolon after goto should be a parse error
        let src = "int main(){ goto L L: return 0; }";
        let res = parse_translation_unit(src);
        assert!(res.is_err());
    }

    #[test]
    fn parse_label_with_decl_and_assign() {
        let src = "int main(){ int x; L: x = 1; return x; }";
        let tu = parse_translation_unit(src).unwrap();
        assert_eq!(tu.functions.len(), 1);
        let f = &tu.functions[0];
        assert_eq!(
            f.body,
            vec![
                Stmt::Decl { name: "x".to_string(), ty: Type::Int, init: None, storage: None, quals: Qualifiers::none() },
                Stmt::Label("L".to_string()),
                Stmt::ExprStmt(Expr::Assign { name: "x".to_string(), value: Box::new(Expr::IntLiteral("1".to_string())) }),
                Stmt::Return(Expr::Ident("x".to_string())),
            ]
        );
    }
}