use parse::*;

fn tu(src: &str) -> TranslationUnit {
    parse_translation_unit(src).expect("parse ok")
}

#[test]
fn parse_switch_basic() {
    let src = r#"
        int main(void) {
            switch (0) { 
                case 1: return 1;
                default: return 2;
            }
        }
    "#;
    let tu = tu(src);
    assert_eq!(tu.functions.len(), 1);
    let f = &tu.functions[0];

    // Expect a single top-level Switch statement
    assert_eq!(f.body.len(), 1);
    match &f.body[0] {
        Stmt::Switch { cond, body } => {
            assert!(matches!(cond, Expr::IntLiteral(ref s) if s == "0"));
            // Body should contain Case(1), Return(1), Default, Return(2)
            assert!(matches!(body[0], Stmt::Case { .. }));
            assert!(matches!(body[1], Stmt::Return(Expr::IntLiteral(ref s)) if s == "1"));
            assert!(matches!(body[2], Stmt::Default));
            assert!(matches!(body[3], Stmt::Return(Expr::IntLiteral(ref s)) if s == "2"));
        }
        other => panic!("expected Switch stmt, got {:?}", other),
    }
}

#[test]
fn parse_switch_fallthrough_multiple_cases() {
    let src = r#"
        int main(void) {
            int y;
            switch (2) { 
                case 1: 
                case 2: y = 3; 
                default: y = 4; 
            }
            return y;
        }
    "#;
    let tu = tu(src);
    let f = &tu.functions[0];
    // Decl, Switch, Return
    assert!(matches!(f.body[0], Stmt::Decl { ref name, .. } if name == "y"));
    match &f.body[1] {
        Stmt::Switch { cond, body } => {
            assert!(matches!(cond, Expr::IntLiteral(ref s) if s == "2"));
            // Expect: Case(1), Case(2), y=3;, Default, y=4;
            assert!(matches!(body[0], Stmt::Case { .. }));
            assert!(matches!(body[1], Stmt::Case { .. }));
            assert!(matches!(body[2], Stmt::ExprStmt(Expr::Assign { ref name, .. }) if name == "y"));
            assert!(matches!(body[3], Stmt::Default));
            assert!(matches!(body[4], Stmt::ExprStmt(Expr::Assign { ref name, .. }) if name == "y"));
        }
        other => panic!("expected Switch stmt, got {:?}", other),
    }
    assert!(matches!(f.body[2], Stmt::Return(Expr::Ident(ref s)) if s == "y"));
}

#[test]
fn parse_switch_nested_in_loop() {
    let src = r#"
        int main(void) {
            while (1) {
                switch (0) { default: return 0; }
            }
        }
    "#;
    let tu = tu(src);
    let f = &tu.functions[0];
    assert_eq!(f.body.len(), 1);
    match &f.body[0] {
        Stmt::While { cond, body } => {
            assert!(matches!(cond, Expr::IntLiteral(ref s) if s == "1"));
            assert_eq!(body.len(), 1);
            match &body[0] {
                Stmt::Switch { cond, body } => {
                    assert!(matches!(cond, Expr::IntLiteral(ref s) if s == "0"));
                    assert_eq!(body.len(), 2);
                    assert!(matches!(body[0], Stmt::Default));
                    assert!(matches!(body[1], Stmt::Return(Expr::IntLiteral(ref s)) if s == "0"));
                }
                other => panic!("expected nested Switch, got {:?}", other),
            }
        }
        other => panic!("expected While, got {:?}", other),
    }
}
