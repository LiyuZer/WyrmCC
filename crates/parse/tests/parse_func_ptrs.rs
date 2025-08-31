use parse::{ast::*, parse_translation_unit};

#[test]
fn indirect_call_via_addr_of_function_parses_as_callptr() {
    let src = r#"
        int add(int a, int b) { return a + b; }
        int main(void) {
            return (*(&add))(2, 3);
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");

    let main_fn = tu
        .functions
        .iter()
        .find(|f| f.name == "main")
        .expect("main present");

    let mut found_callptr = false;
    for s in &main_fn.body {
        if let Stmt::Return(e) = s {
            match e {
                Expr::CallPtr { target, args } => {
                    if let Expr::Unary {
                        op: UnaryOp::Deref,
                        expr,
                    } = target.as_ref()
                    {
                        if let Expr::Unary {
                            op: UnaryOp::AddrOf,
                            expr: inner,
                        } = expr.as_ref()
                        {
                            if let Expr::Ident(name) = inner.as_ref() {
                                assert_eq!(name, "add");
                                assert_eq!(args.len(), 2);
                                found_callptr = true;
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    assert!(found_callptr, "expected CallPtr in return expression");
}
