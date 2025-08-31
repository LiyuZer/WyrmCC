use parse::*;

// Parenthesized declarators and abstract declarators coverage

#[test]
fn parse_local_pointer_to_array_paren_decl_parses() {
    let src = r#"
        int main(){
            int (*p)[3];
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.functions.len(), 1);
    let f = &tu.functions[0];
    // Expect first stmt to be declaration of: int (*p)[3];
    match &f.body[0] {
        Stmt::Decl { name, ty, .. } => {
            assert_eq!(name, "p");
            assert_eq!(
                ty,
                &Type::Pointer(Box::new(Type::Array(Box::new(Type::Int), 3)))
            );
        }
        other => panic!("expected decl for pointer-to-array, got {:?}", other),
    }
}

#[test]
fn parse_cast_to_function_pointer_abstract_declarator() {
    let src = r#"
        int main(){
            (int (*)(int))0;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];
    // First statement should be an expression statement with a Cast to function-pointer type
    match &f.body[0] {
        Stmt::ExprStmt(Expr::Cast { ty, expr }) => {
            assert_eq!(
                ty,
                &Type::Pointer(Box::new(Type::Func {
                    ret: Box::new(Type::Int),
                    params: vec![Type::Int],
                    variadic: false,
                }))
            );
            // expr can be any integer literal 0
            match &**expr {
                Expr::IntLiteral(s) => assert_eq!(s, "0"),
                other => panic!("expected int literal in cast, got {:?}", other),
            }
        }
        other => panic!("expected cast to function pointer, got {:?}", other),
    }
}

#[test]
fn parse_cast_to_pointer_to_array_abstract_declarator() {
    let src = r#"
        int main(){
            (int (*)[3])0;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];
    match &f.body[0] {
        Stmt::ExprStmt(Expr::Cast { ty, expr }) => {
            assert_eq!(
                ty,
                &Type::Pointer(Box::new(Type::Array(Box::new(Type::Int), 3)))
            );
            match &**expr {
                Expr::IntLiteral(s) => assert_eq!(s, "0"),
                other => panic!("expected int literal in cast, got {:?}", other),
            }
        }
        other => panic!("expected cast to pointer-to-array, got {:?}", other),
    }
}

#[test]
fn parse_typedef_pointer_to_array_inside_function() {
    let src = r#"
        int main(){
            typedef int (*P)[3];
            P a;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];
    // Expect first stmt is typedef of pointer-to-array, second is decl using it
    match &f.body[0] {
        Stmt::Typedef { name, ty } => {
            assert_eq!(name, "P");
            assert_eq!(
                ty,
                &Type::Pointer(Box::new(Type::Array(Box::new(Type::Int), 3)))
            );
        }
        other => panic!("expected typedef of pointer-to-array, got {:?}", other),
    }
    match &f.body[1] {
        Stmt::Decl { name, ty, .. } => {
            assert_eq!(name, "a");
            // The declared type is the typedef-name; sema will resolve it.
            assert_eq!(ty, &Type::Named("P".to_string()));
        }
        other => panic!("expected declaration using typedef P, got {:?}", other),
    }
}
