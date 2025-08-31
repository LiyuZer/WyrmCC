use parse::{ast::*, parse_translation_unit};

fn find_main(tu: &TranslationUnit) -> &Function {
    tu.functions.iter().find(|f| f.name == "main").expect("main not found")
}

#[test]
fn local_int_array_brace_init() {
    let src = r#"
        int main(void) {
            int a[3] = {1,2,3};
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = find_main(&tu);
    // decl 0: int a[3] = {1,2,3}
    match &f.body[0] {
        Stmt::Decl { name, ty, init, .. } => {
            assert_eq!(name, "a");
            match ty {
                Type::Array(inner, n) => {
                    assert_eq!(*n, 3);
                    assert!(matches!(**inner, Type::Int));
                }
                other => panic!("expected array type, got {:?}", other),
            }
            match init {
                Some(Expr::InitList(items)) => {
                    assert_eq!(items.len(), 3);
                    assert!(matches!(items[0], Expr::IntLiteral(ref s) if s == "1"));
                    assert!(matches!(items[1], Expr::IntLiteral(ref s) if s == "2"));
                    assert!(matches!(items[2], Expr::IntLiteral(ref s) if s == "3"));
                }
                other => panic!("expected InitList, got {:?}", other),
            }
        }
        other => panic!("expected decl a, got {:?}", other),
    }
}

#[test]
fn local_unsized_int_array_brace_init() {
    let src = r#"
        int main(void) {
            int a[] = {1,2,3};
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = find_main(&tu);
    match &f.body[0] {
        Stmt::Decl { name, ty, init, .. } => {
            assert_eq!(name, "a");
            match ty {
                Type::Array(inner, n) => {
                    assert_eq!(*n, 0, "unsized arrays parse as size 0 (inferred later)" );
                    assert!(matches!(**inner, Type::Int));
                }
                other => panic!("expected array type, got {:?}", other),
            }
            assert!(matches!(init, Some(Expr::InitList(items)) if items.len() == 3));
        }
        other => panic!("expected decl a, got {:?}", other),
    }
}

#[test]
fn local_struct_brace_init() {
    let src = r#"
        int main(void) {
            struct S { int a; int b; };
            struct S s = {1,2};
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = find_main(&tu);
    match &f.body[1] {
        Stmt::Decl { name, ty, init, .. } => {
            assert_eq!(name, "s");
            assert!(matches!(ty, Type::Struct(ref tag) if tag == "S"));
            match init {
                Some(Expr::InitList(items)) => {
                    assert_eq!(items.len(), 2);
                    assert!(matches!(items[0], Expr::IntLiteral(ref s) if s == "1"));
                    assert!(matches!(items[1], Expr::IntLiteral(ref s) if s == "2"));
                }
                other => panic!("expected InitList for struct, got {:?}", other),
            }
        }
        other => panic!("expected decl s, got {:?}", other),
    }
}

#[test]
fn array_of_structs_nested_init() {
    let src = r#"
        int main(void) {
            struct S { int a; int b; };
            struct S t[2] = {{1,2},{3,4}};
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = find_main(&tu);
    match &f.body[1] {
        Stmt::Decl { name, ty, init, .. } => {
            assert_eq!(name, "t");
            match ty {
                Type::Array(inner, n) => {
                    assert_eq!(*n, 2);
                    assert!(matches!(**inner, Type::Struct(ref tag) if tag == "S"));
                }
                other => panic!("expected array of struct type, got {:?}", other),
            }
            match init {
                Some(Expr::InitList(items)) => {
                    assert_eq!(items.len(), 2);
                    for (i, it) in items.iter().enumerate() {
                        match it {
                            Expr::InitList(pair) => {
                                assert_eq!(pair.len(), 2);
                                let a = match &pair[0] { Expr::IntLiteral(s) => s.clone(), _ => panic!("expected int") };
                                let b = match &pair[1] { Expr::IntLiteral(s) => s.clone(), _ => panic!("expected int") };
                                match i { 0 => { assert_eq!(a, "1"); assert_eq!(b, "2"); }, 1 => { assert_eq!(a, "3"); assert_eq!(b, "4"); }, _ => unreachable!() }
                            }
                            other => panic!("expected nested InitList, got {:?}", other),
                        }
                    }
                }
                other => panic!("expected InitList for array-of-structs, got {:?}", other),
            }
        }
        other => panic!("expected decl t, got {:?}", other),
    }
}

#[test]
fn trailing_commas_in_init_lists() {
    let src = r#"
        int main(void) {
            int a[3] = {1,2,3,};
            struct S { int a; int b; };
            struct S s = {1,2,};
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = find_main(&tu);
    // a
    match &f.body[0] {
        Stmt::Decl { name, init, .. } => {
            assert_eq!(name, "a");
            match init {
                Some(Expr::InitList(items)) => assert_eq!(items.len(), 3),
                other => panic!("expected InitList, got {:?}", other),
            }
        }
        other => panic!("expected decl a, got {:?}", other),
    }
    // s
    match &f.body[2] {
        Stmt::Decl { name, init, .. } => {
            assert_eq!(name, "s");
            match init {
                Some(Expr::InitList(items)) => assert_eq!(items.len(), 2),
                other => panic!("expected InitList, got {:?}", other),
            }
        }
        other => panic!("expected decl s, got {:?}", other),
    }
}

#[test]
fn char_array_string_literal_inits() {
    let src = r#"
        int main(void) {
            char s[] = "hi";
            char s2[5] = "hi";
            char s3[2] = "hi"; // size check is sema's job; parser should accept
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = find_main(&tu);
    // s
    match &f.body[0] {
        Stmt::Decl { name, ty, init, .. } => {
            assert_eq!(name, "s");
            match ty { Type::Array(inner, n) => { assert_eq!(*n, 0); assert!(matches!(**inner, Type::Char)); }, other => panic!("expected char[], got {:?}", other) }
            assert!(matches!(init, Some(Expr::StringLiteral(_))));
        }
        other => panic!("expected decl s, got {:?}", other),
    }
    // s2
    match &f.body[1] {
        Stmt::Decl { name, ty, init, .. } => {
            assert_eq!(name, "s2");
            match ty { Type::Array(inner, n) => { assert_eq!(*n, 5); assert!(matches!(**inner, Type::Char)); }, other => panic!("expected char[5], got {:?}", other) }
            assert!(matches!(init, Some(Expr::StringLiteral(_))));
        }
        other => panic!("expected decl s2, got {:?}", other),
    }
    // s3
    match &f.body[2] {
        Stmt::Decl { name, ty, init, .. } => {
            assert_eq!(name, "s3");
            match ty { Type::Array(inner, n) => { assert_eq!(*n, 2); assert!(matches!(**inner, Type::Char)); }, other => panic!("expected char[2], got {:?}", other) }
            assert!(matches!(init, Some(Expr::StringLiteral(_))));
        }
        other => panic!("expected decl s3, got {:?}", other),
    }
}

#[test]
fn nested_struct_with_array_init() {
    let src = r#"
        int main(void) {
            struct T { int a[2]; int b; } s = {{1,2}, 3};
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = find_main(&tu);
    match &f.body[0] {
        Stmt::Decl { name, ty, init, .. } => {
            assert_eq!(name, "s");
            assert!(matches!(ty, Type::Struct(ref tag) if tag == "T" || tag == ""));
            match init {
                Some(Expr::InitList(items)) => {
                    assert_eq!(items.len(), 2);
                    match &items[0] { Expr::InitList(arr) => { assert_eq!(arr.len(), 2); }, other => panic!("expected inner InitList for array, got {:?}", other) }
                    assert!(matches!(items[1], Expr::IntLiteral(ref s) if s == "3"));
                }
                other => panic!("expected InitList, got {:?}", other),
            }
        }
        other => panic!("expected decl s, got {:?}", other),
    }
}
