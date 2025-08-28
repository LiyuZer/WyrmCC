use parse::{parse_translation_unit};
use parse::ast::{Type, Expr, Storage};

#[test]
fn parse_global_int_init() {
    let src = r#"
        int g = 42;
        int main(void) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");

    assert_eq!(tu.globals.len(), 1, "expected 1 global, got {}", tu.globals.len());
    let g = &tu.globals[0];
    assert_eq!(g.name, "g");
    assert!(matches!(g.ty, Type::Int));
    assert!(matches!(g.init, Some(Expr::IntLiteral(ref s)) if s == "42"));
    assert!(g.storage.is_none());
    assert_eq!(tu.functions.len(), 1, "expected 1 function definition");
}

#[test]
fn parse_global_zero_init() {
    let src = r#"
        int g;
        int main(void) { return g; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");

    assert_eq!(tu.globals.len(), 1);
    let g = &tu.globals[0];
    assert_eq!(g.name, "g");
    assert!(matches!(g.ty, Type::Int));
    assert!(g.init.is_none());
    assert!(g.storage.is_none());
}

#[test]
fn parse_extern_decl() {
    let src = r#"
        extern int g;
        int main(void) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");

    assert_eq!(tu.globals.len(), 1);
    let g = &tu.globals[0];
    assert_eq!(g.name, "g");
    assert!(matches!(g.ty, Type::Int));
    assert!(matches!(g.storage, Some(Storage::Extern)));
}

#[test]
fn parse_global_pointer_to_string_cast() {
    let src = r#"
        int *p = (int*)"hi";
        int main(void) { return p != 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");

    assert_eq!(tu.globals.len(), 1);
    let p = &tu.globals[0];
    assert_eq!(p.name, "p");
    // type should be pointer to int
    match &p.ty {
        Type::Pointer(inner) => assert!(matches!(**inner, Type::Int)),
        other => panic!("expected pointer type for p, got {:?}", other),
    }
    // init should be a cast of a string literal to (int*)
    match &p.init {
        Some(Expr::Cast { ty, expr }) => {
            match ty {
                Type::Pointer(inner) => assert!(matches!(**inner, Type::Int)),
                other => panic!("expected cast to pointer-to-int, got {:?}", other),
            }
            match expr.as_ref() {
                Expr::StringLiteral(_) => {},
                other => panic!("expected string literal in cast init, got {:?}", other),
            }
        }
        other => panic!("expected cast initializer, got {:?}", other),
    }
}

#[test]
fn parse_global_array_decl() {
    let src = r#"
        int a[3];
        int main(void) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");

    assert_eq!(tu.globals.len(), 1);
    let a = &tu.globals[0];
    assert_eq!(a.name, "a");
    match &a.ty {
        Type::Array(inner, n) => {
            assert!(matches!(**inner, Type::Int));
            assert_eq!(*n, 3usize);
        }
        other => panic!("expected int array type, got {:?}", other),
    }
}
