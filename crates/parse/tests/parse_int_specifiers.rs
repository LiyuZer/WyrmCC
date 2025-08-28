use parse::parse_translation_unit;
use parse::ast::{Stmt, Type};

fn find_decl<'a>(stmts: &'a [Stmt], name: &str) -> Option<(&'a String, &'a Type)> {
    for s in stmts {
        match s {
            Stmt::Decl { name: n, ty, .. } if n == name => return Some((n, ty)),
            Stmt::Block(b) => if let Some(found) = find_decl(b, name) { return Some(found); },
            _ => {}
        }
    }
    None
}

#[test]
fn parse_basic_integer_specifiers_as_int() {
    let src = r#"
        int main(void) {
            unsigned ux;
            signed sx;
            short sh;
            long lg;
            char ch;
            int ix;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];

    for name in ["ux","sx","sh","lg","ch","ix"] {
        let (_n, ty) = find_decl(&f.body, name).expect("decl found");
        assert!(matches!(ty, Type::Int), "{} should be parsed as Type::Int, got {:?}", name, ty);
    }
}

#[test]
fn parse_combined_specifiers_map_to_int() {
    let src = r#"
        int main(void) {
            unsigned int a;
            short int b;
            signed long int c;
            long int d;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];

    for name in ["a","b","c","d"] {
        let (_n, ty) = find_decl(&f.body, name).expect("decl found");
        assert!(matches!(ty, Type::Int), "{} should be Type::Int, got {:?}", name, ty);
    }
}

#[test]
fn parse_pointer_and_array_forms() {
    let src = r#"
        int main(void) {
            unsigned *p;
            short arr[3];
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];

    let (_np, typ) = find_decl(&f.body, "p").expect("p decl");
    match typ {
        Type::Pointer(inner) => assert!(matches!(&**inner, Type::Int), "pointer base should be int, got {:?}", inner),
        other => panic!("expected pointer type for p, got {:?}", other),
    }

    let (_na, ty_arr) = find_decl(&f.body, "arr").expect("arr decl");
    match ty_arr {
        Type::Array(inner, n) => {
            assert!(matches!(&**inner, Type::Int), "array element type should be int, got {:?}", inner);
            assert_eq!(*n, 3, "array size should be 3");
        }
        other => panic!("expected array type for arr, got {:?}", other),
    }
}
