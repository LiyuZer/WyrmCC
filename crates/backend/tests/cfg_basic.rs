use backend::emit_llvm_ir;
use parse::ast::*;

fn ir_for(tu: &TranslationUnit) -> String {
    emit_llvm_ir(tu, "test_mod").expect("emit ok")
}

#[test]
fn if_else_ir_patterns() {
    // int main(){ int x=1; if(x){ return 2; } else { return 3; } }
    let tu = TranslationUnit {
        functions: vec![Function {
            name: "main".into(),
            ret_type: Type::Int,
            params: vec![],
            body: vec![
                Stmt::Decl { name: "x".into(), ty: Type::Int, init: Some(Expr::IntLiteral("1".into())) },
                Stmt::If {
                    cond: Expr::Ident("x".into()),
                    then_branch: vec![Stmt::Return(Expr::IntLiteral("2".into()))],
                    else_branch: Some(vec![Stmt::Return(Expr::IntLiteral("3".into()))]),
                },
            ],
        }],
        records: vec![],
        enums: vec![],
        globals: vec![],
    };

    let ir = ir_for(&tu);
    // Should produce compare to zero for x, a conditional branch, labels, and both returns.
    assert!(ir.contains("icmp ne i32"), "expected integer-to-bool compare in IR:\n{}", ir);
    assert!(ir.contains(" br i1 "), "expected conditional branch in IR:\n{}", ir);
    assert!(ir.contains("\nL") && ir.contains(":"), "expected label blocks in IR:\n{}", ir);
    assert!(ir.contains("ret i32 2") && ir.contains("ret i32 3"), "expected both return values in IR:\n{}", ir);
}

#[test]
fn while_break_continue_patterns() {
    // int main(){ int i=0; while(i<3){ if(i==1){ i=i+1; continue; } if(i==2) break; i=i+1; } return i; }
    let tu = TranslationUnit {
        functions: vec![Function {
            name: "main".into(),
            ret_type: Type::Int,
            params: vec![],
            body: vec![
                Stmt::Decl { name: "i".into(), ty: Type::Int, init: Some(Expr::IntLiteral("0".into())) },
                Stmt::While {
                    cond: Expr::Binary {
                        op: BinaryOp::Lt,
                        lhs: Box::new(Expr::Ident("i".into())),
                        rhs: Box::new(Expr::IntLiteral("3".into())),
                    },
                    body: vec![
                        Stmt::If {
                            cond: Expr::Binary {
                                op: BinaryOp::Eq,
                                lhs: Box::new(Expr::Ident("i".into())),
                                rhs: Box::new(Expr::IntLiteral("1".into())),
                            },
                            then_branch: vec![
                                Stmt::ExprStmt(Expr::Assign {
                                    name: "i".into(),
                                    value: Box::new(Expr::Binary {
                                        op: BinaryOp::Plus,
                                        lhs: Box::new(Expr::Ident("i".into())),
                                        rhs: Box::new(Expr::IntLiteral("1".into())),
                                    }),
                                }),
                                Stmt::Continue,
                            ],
                            else_branch: None,
                        },
                        Stmt::If {
                            cond: Expr::Binary {
                                op: BinaryOp::Eq,
                                lhs: Box::new(Expr::Ident("i".into())),
                                rhs: Box::new(Expr::IntLiteral("2".into())),
                            },
                            then_branch: vec![Stmt::Break],
                            else_branch: None,
                        },
                        Stmt::ExprStmt(Expr::Assign {
                            name: "i".into(),
                            value: Box::new(Expr::Binary {
                                op: BinaryOp::Plus,
                                lhs: Box::new(Expr::Ident("i".into())),
                                rhs: Box::new(Expr::IntLiteral("1".into())),
                            }),
                        }),
                    ],
                },
                Stmt::Return(Expr::Ident("i".into())),
            ],
        }],
        records: vec![],
        enums: vec![],
        globals: vec![],
    };

    let ir = ir_for(&tu);
    // Expect control-flow structure present
    assert!(ir.contains("icmp") && ir.matches(" br ").count() > 1, "expected multiple branches in IR:\n{}", ir);
    assert!(ir.contains("\nL") && ir.contains(":"), "expected several labels in IR:\n{}", ir);
    // The loop should have a backedge or uncond branch to a label
    assert!(ir.contains("br label %L"), "expected backedge or uncond branch to a label:\n{}", ir);
}