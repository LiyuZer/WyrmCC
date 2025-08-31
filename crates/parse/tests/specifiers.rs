use parse::ast::Type;
use parse::parse_translation_unit;

fn decl_type(src: &str, name: &str) -> Type {
    let tu = parse_translation_unit(src).expect("parse ok");
    let g = tu
        .globals
        .iter()
        .find(|g| g.name == name)
        .expect("decl present");
    g.ty.clone()
}

#[test]
fn char_family() {
    assert!(matches!(decl_type("char c;", "c"), Type::Char));
    assert!(matches!(decl_type("signed char sc;", "sc"), Type::SChar));
    assert!(matches!(decl_type("unsigned char uc;", "uc"), Type::UChar));
}

#[test]
fn short_family() {
    assert!(matches!(decl_type("short s;", "s"), Type::Short));
    assert!(matches!(decl_type("short int s;", "s"), Type::Short));
    assert!(matches!(decl_type("signed short ss;", "ss"), Type::Short));
    assert!(matches!(
        decl_type("unsigned short us;", "us"),
        Type::UShort
    ));
}

#[test]
fn int_family() {
    assert!(matches!(decl_type("int i;", "i"), Type::Int));
    assert!(matches!(decl_type("signed si;", "si"), Type::Int));
    assert!(matches!(decl_type("signed int si;", "si"), Type::Int));
    assert!(matches!(decl_type("unsigned ui;", "ui"), Type::UInt));
    assert!(matches!(decl_type("unsigned int ui;", "ui"), Type::UInt));
}

#[test]
fn long_family() {
    assert!(matches!(decl_type("long l;", "l"), Type::Long));
    assert!(matches!(decl_type("long int l;", "l"), Type::Long));
    assert!(matches!(decl_type("signed long sl;", "sl"), Type::Long));
    assert!(matches!(decl_type("unsigned long ul;", "ul"), Type::ULong));
}

#[test]
fn defaults_and_pointers() {
    // Bare signed/unsigned default to (un)signed int
    assert!(matches!(decl_type("signed s;", "s"), Type::Int));
    assert!(matches!(decl_type("unsigned u;", "u"), Type::UInt));

    // Pointer suffix keeps base kind
    assert!(matches!(
        decl_type("unsigned long *p;", "p"),
        Type::Pointer(inner) if matches!(*inner, Type::ULong)
    ));
}

#[test]
fn params_types() {
    let src = r#"
        int f(unsigned short x, signed char y, long z) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = tu.functions.iter().find(|f| f.name == "f").expect("fn f");
    assert_eq!(f.params.len(), 3);
    assert!(matches!(f.params[0].ty, Type::UShort));
    assert!(matches!(f.params[1].ty, Type::SChar));
    assert!(matches!(f.params[2].ty, Type::Long));
}
