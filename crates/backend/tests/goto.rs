use backend::{emit_llvm_ir, verify_llvm_text};
use parse::ast::*;

fn ir_for(tu: &TranslationUnit) -> String {
    emit_llvm_ir(tu, "test_mod").expect("emit ok")
}

fn verify_ok(ir: &str) {
    verify_llvm_text(ir).expect("llvm text verifier ok");
}

#[test]
fn goto_forward() {
    // int main(){ int x=1; goto L1; x=2; L1: return 3; }
    let tu = TranslationUnit {
        functions: vec![Function {
            name: "main".into(),
            ret_type: Type::Int,
            params: vec![],
            variadic: false,
            body: vec![
                Stmt::Decl { name: "x".into(), ty: Type::Int, init: Some(Expr::IntLiteral("1".into())), storage: None, quals: Qualifiers::none() },
                Stmt::Goto("L1".into()),
                Stmt::ExprStmt(Expr::Assign { name: "x".into(), value: Box::new(Expr::IntLiteral("2".into())) }),
                Stmt::Label("L1".into()),
                Stmt::Return(Expr::IntLiteral("3".into())),
            ],
            storage: None,
        }],
        records: vec![],
        enums: vec![],
        globals: vec![],
    };

    let ir = ir_for(&tu);
    verify_ok(&ir);
    assert!(ir.contains("br label %L"), "expected unconditional branch to a label in IR\n{}", ir);
    assert!(ir.contains("\nL") && ir.contains(":"), "expected label blocks in IR\n{}", ir);
}

#[test]
fn goto_backward_loop() {
    // int main(){ int i=0; L0: i=i+1; if(i<3) goto L0; return i; }
    let tu = TranslationUnit {
        functions: vec![Function {
            name: "main".into(),
            ret_type: Type::Int,
            params: vec![],
            variadic: false,
            body: vec![
                Stmt::Decl { name: "i".into(), ty: Type::Int, init: Some(Expr::IntLiteral("0".into())), storage: None, quals: Qualifiers::none() },
                Stmt::Label("L0".into()),
                Stmt::ExprStmt(Expr::Assign {
                    name: "i".into(),
                    value: Box::new(Expr::Binary {
                        op: BinaryOp::Plus,
                        lhs: Box::new(Expr::Ident("i".into())),
                        rhs: Box::new(Expr::IntLiteral("1".into())),
                    }),
                }),
                Stmt::If {
                    cond: Expr::Binary {
                        op: BinaryOp::Lt,
                        lhs: Box::new(Expr::Ident("i".into())),
                        rhs: Box::new(Expr::IntLiteral("3".into())),
                    },
                    then_branch: vec![Stmt::Goto("L0".into())],
                    else_branch: None,
                },
                Stmt::Return(Expr::Ident("i".into())),
            ],
            storage: None,
        }],
        records: vec![],
        enums: vec![],
        globals: vec![],
    };

    let ir = ir_for(&tu);
    verify_ok(&ir);
    assert!(ir.contains("br label %L"), "expected branch to label (backedge) in IR\n{}", ir);
}

#[test]
fn consecutive_labels() {
    // int main(){ int i=0; L1: L2: i=1; goto end; L3: i=2; end: return i; }
    let tu = TranslationUnit {
        functions: vec![Function {
            name: "main".into(),
            ret_type: Type::Int,
            params: vec![],
            variadic: false,
            body: vec![
                Stmt::Decl { name: "i".into(), ty: Type::Int, init: Some(Expr::IntLiteral("0".into())), storage: None, quals: Qualifiers::none() },
                Stmt::Label("L1".into()),
                Stmt::Label("L2".into()),
                Stmt::ExprStmt(Expr::Assign { name: "i".into(), value: Box::new(Expr::IntLiteral("1".into())) }),
                Stmt::Goto("end".into()),
                Stmt::Label("L3".into()),
                Stmt::ExprStmt(Expr::Assign { name: "i".into(), value: Box::new(Expr::IntLiteral("2".into())) }),
                Stmt::Label("end".into()),
                Stmt::Return(Expr::Ident("i".into())),
            ],
            storage: None,
        }],
        records: vec![],
        enums: vec![],
        globals: vec![],
    };

    let ir = ir_for(&tu);
    verify_ok(&ir);
    // Ensure labels exist and are well-formed
    assert!(ir.matches("\nL").count() >= 2, "expected multiple consecutive label blocks in IR\n{}", ir);
}

#[test]
fn goto_across_if() {
    // int main(){ int x=1; if(x){ goto out; } int y=5; out: return x; }
    let tu = TranslationUnit {
        functions: vec![Function {
            name: "main".into(),
            ret_type: Type::Int,
            params: vec![],
            variadic: false,
            body: vec![
                Stmt::Decl { name: "x".into(), ty: Type::Int, init: Some(Expr::IntLiteral("1".into())), storage: None, quals: Qualifiers::none() },
                Stmt::If {
                    cond: Expr::Ident("x".into()),
                    then_branch: vec![Stmt::Goto("out".into())],
                    else_branch: None,
                },
                Stmt::Decl { name: "y".into(), ty: Type::Int, init: Some(Expr::IntLiteral("5".into())), storage: None, quals: Qualifiers::none() },
                Stmt::Label("out".into()),
                Stmt::Return(Expr::Ident("x".into())),
            ],
            storage: None,
        }],
        records: vec![],
        enums: vec![],
        globals: vec![],
    };

    let ir = ir_for(&tu);
    verify_ok(&ir);
    assert!(ir.contains(" br i1 ") || ir.contains("icmp"), "expected conditional branch and compare in IR\n{}", ir);
    assert!(ir.contains("br label %L"), "expected branch to label across if\n{}", ir);
}

#[test]
fn goto_with_return() {
    // int main(){ if(1) return 7; L1: return 0; }
    let tu = TranslationUnit {
        functions: vec![Function {
            name: "main".into(),
            ret_type: Type::Int,
            params: vec![],
            variadic: false,
            body: vec![
                Stmt::If {
                    cond: Expr::IntLiteral("1".into()),
                    then_branch: vec![Stmt::Return(Expr::IntLiteral("7".into()))],
                    else_branch: None,
                },
                Stmt::Label("L1".into()),
                Stmt::Return(Expr::IntLiteral("0".into())),
            ],
            storage: None,
        }],
        records: vec![],
        enums: vec![],
        globals: vec![],
    };

    let ir = ir_for(&tu);
    verify_ok(&ir);
    assert!(ir.contains("ret i32 7"), "expected early return before label\n{}", ir);
    assert!(ir.contains("\nL") && ir.contains(":"), "expected labeled block after return\n{}", ir);
}