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
fn parse_basic_integer_specifiers_full_fidelity() {
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

    // unsigned -> UInt
    let (_n, ty) = find_decl(&f.body, "ux").expect("ux decl");
    assert!(matches!(ty, Type::UInt), "ux should be UInt, got {:?}", ty);

    // signed -> Int (signed int)
    let (_n, ty) = find_decl(&f.body, "sx").expect("sx decl");
    assert!(matches!(ty, Type::Int), "sx should be Int, got {:?}", ty);

    // short -> Short
    let (_n, ty) = find_decl(&f.body, "sh").expect("sh decl");
    assert!(matches!(ty, Type::Short), "sh should be Short, got {:?}", ty);

    // long -> Long
    let (_n, ty) = find_decl(&f.body, "lg").expect("lg decl");
    assert!(matches!(ty, Type::Long), "lg should be Long, got {:?}", ty);

    // char -> Char (implementation-defined signedness; distinct from SChar/UChar)
    let (_n, ty) = find_decl(&f.body, "ch").expect("ch decl");
    assert!(matches!(ty, Type::Char), "ch should be Char, got {:?}", ty);

    // int -> Int
    let (_n, ty) = find_decl(&f.body, "ix").expect("ix decl");
    assert!(matches!(ty, Type::Int), "ix should be Int, got {:?}", ty);
}

#[test]
fn parse_combined_specifiers_full_fidelity() {
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

    // unsigned int -> UInt
    let (_n, ty) = find_decl(&f.body, "a").expect("a decl");
    assert!(matches!(ty, Type::UInt), "a should be UInt, got {:?}", ty);

    // short int -> Short
    let (_n, ty) = find_decl(&f.body, "b").expect("b decl");
    assert!(matches!(ty, Type::Short), "b should be Short, got {:?}", ty);

    // signed long int -> Long
    let (_n, ty) = find_decl(&f.body, "c").expect("c decl");
    assert!(matches!(ty, Type::Long), "c should be Long, got {:?}", ty);

    // long int -> Long
    let (_n, ty) = find_decl(&f.body, "d").expect("d decl");
    assert!(matches!(ty, Type::Long), "d should be Long, got {:?}", ty);
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
        Type::Pointer(inner) => assert!(matches!(&**inner, Type::UInt), "pointer base should be UInt, got {:?}", inner),
        other => panic!("expected pointer type for p, got {:?}", other),
    }

    let (_na, ty_arr) = find_decl(&f.body, "arr").expect("arr decl");
    match ty_arr {
        Type::Array(inner, n) => {
            assert!(matches!(&**inner, Type::Short), "array element type should be Short, got {:?}", inner);
            assert_eq!(*n, 3, "array size should be 3");
        }
        other => panic!("expected array type for arr, got {:?}", other),
    }
}

#[test]
fn parse_char_signedness_and_unsigned_widths() {
    let src = r#"
        int main(void) {
            signed char sc;
            unsigned char uc;
            unsigned short us;
            unsigned long ul;
            long long llv; // C99 extension; here collapses to Long (C89 project model)
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = &tu.functions[0];

    let (_n, ty) = find_decl(&f.body, "sc").expect("sc decl");
    assert!(matches!(ty, Type::SChar), "sc should be SChar, got {:?}", ty);

    let (_n, ty) = find_decl(&f.body, "uc").expect("uc decl");
    assert!(matches!(ty, Type::UChar), "uc should be UChar, got {:?}", ty);

    let (_n, ty) = find_decl(&f.body, "us").expect("us decl");
    assert!(matches!(ty, Type::UShort), "us should be UShort, got {:?}", ty);

    let (_n, ty) = find_decl(&f.body, "ul").expect("ul decl");
    assert!(matches!(ty, Type::ULong), "ul should be ULong, got {:?}", ty);

    // long long -> Long (no separate LongLong in this C89 subset; duplicates collapse)
    let (_n, ty) = find_decl(&f.body, "llv").expect("llv decl");
    assert!(matches!(ty, Type::Long), "llv should be Long, got {:?}", ty);
}