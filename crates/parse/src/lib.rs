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
                Stmt::Decl {
                    name: "x".to_string(),
                    ty: Type::Int,
                    init: None,
                    storage: None,
                    quals: Qualifiers::none()
                },
                Stmt::Label("L".to_string()),
                Stmt::ExprStmt(Expr::Assign {
                    name: "x".to_string(),
                    value: Box::new(Expr::IntLiteral("1".to_string()))
                }),
                Stmt::Return(Expr::Ident("x".to_string())),
            ]
        );
    }
}

#[cfg(test)]
mod init_list_tests {
    use super::*;

    // ===== Initializer list parse tests (v2) =====
    #[test]
    fn parse_global_array_init_list_v2() {
        let src = r#"
            int a[3] = {1,2,3};
            int main(void) { return 0; }
        "#;
        let tu = parse_translation_unit(src).expect("parse ok");
        assert_eq!(tu.globals.len(), 1);
        let g = &tu.globals[0];
        assert_eq!(g.name, "a");
        assert_eq!(g.ty, Type::Array(Box::new(Type::Int), 3));
        match &g.init {
            Some(Expr::InitList(items)) => {
                assert_eq!(
                    items,
                    &vec![
                        Expr::IntLiteral("1".to_string()),
                        Expr::IntLiteral("2".to_string()),
                        Expr::IntLiteral("3".to_string()),
                    ]
                );
            }
            other => panic!("expected InitList, got {:?}", other),
        }
    }

    #[test]
    fn parse_global_nested_array_init_list_v2() {
        let src = r#"
            int b[2][2] = { {1,2}, {3,4} };
            int main(void) { return 0; }
        "#;
        let tu = parse_translation_unit(src).expect("parse ok");
        assert_eq!(tu.globals.len(), 1);
        let g = &tu.globals[0];
        assert_eq!(g.name, "b");
        // Type should be int[2][2] (right-to-left nesting)
        assert_eq!(
            g.ty,
            Type::Array(Box::new(Type::Array(Box::new(Type::Int), 2)), 2)
        );
        match &g.init {
            Some(Expr::InitList(items)) => {
                // Outer list has two items
                assert_eq!(items.len(), 2);
                // Each inner item should be an InitList with two ints
                for (i, inner) in items.iter().enumerate() {
                    match inner {
                        Expr::InitList(inner_items) => {
                            assert_eq!(inner_items.len(), 2, "inner[{}] length", i);
                        }
                        other => panic!("expected nested InitList, got {:?}", other),
                    }
                }
            }
            other => panic!("expected InitList, got {:?}", other),
        }
    }

    #[test]
    fn parse_global_struct_init_list_v2() {
        let src = r#"
            struct S { int x; int y; };
            struct S s = {1, 2};
            int main(void) { return 0; }
        "#;
        let tu = parse_translation_unit(src).expect("parse ok");
        // We expect exactly one initialized global (the struct instance)
        assert_eq!(tu.globals.len(), 1);
        let g = &tu.globals[0];
        assert_eq!(g.name, "s");
        assert_eq!(g.ty, Type::Struct("S".to_string()));
        match &g.init {
            Some(Expr::InitList(items)) => {
                assert_eq!(items.len(), 2);
            }
            other => panic!("expected InitList for struct, got {:?}", other),
        }
    }

    #[test]
    fn parse_char_array_unsized_from_string_v2() {
        let src = r#"
            char s[] = "hi";
            int main(void) { return 0; }
        "#;
        let tu = parse_translation_unit(src);
        // Parser allows unsized [] declarators (size 0 sentinel)
        let tu = tu.expect("parse ok");
        assert_eq!(tu.globals.len(), 1);
        let g = &tu.globals[0];
        assert_eq!(g.name, "s");
        assert_eq!(g.ty, Type::Array(Box::new(Type::Char), 0));
        match &g.init {
            Some(Expr::StringLiteral(s)) => {
                // Lexer provides string literal repr including quotes
                assert_eq!(s, &"\"hi\"".to_string());
            }
            other => panic!("expected StringLiteral init, got {:?}", other),
        }
    }
}