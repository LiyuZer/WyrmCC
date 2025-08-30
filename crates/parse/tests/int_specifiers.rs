use parse::{parse_translation_unit, ast::Type};

fn ty_of_global(src: &str, name: &str) -> Type {
    let tu = parse_translation_unit(src).expect("parse tu");
    let g = tu
        .globals
        .iter()
        .find(|g| g.name == name)
        .expect("global not found");
    g.ty.clone()
}

#[test]
fn char_kinds() {
    let src = r#"
        signed char a;
        unsigned char b;
        char c;
    "#;
    assert_eq!(ty_of_global(src, "a"), Type::SChar);
    assert_eq!(ty_of_global(src, "b"), Type::UChar);
    assert_eq!(ty_of_global(src, "c"), Type::Char);
}

#[test]
fn short_and_long_kinds() {
    let src = r#"
        short s;
        unsigned short us;
        long l;
        unsigned long ul;
    "#;
    assert_eq!(ty_of_global(src, "s"), Type::Short);
    assert_eq!(ty_of_global(src, "us"), Type::UShort);
    assert_eq!(ty_of_global(src, "l"), Type::Long);
    assert_eq!(ty_of_global(src, "ul"), Type::ULong);
}

#[test]
fn int_family_signedness() {
    let src = r#"
        int a;
        unsigned int b;
        unsigned c;
        signed d;
    "#;
    assert_eq!(ty_of_global(src, "a"), Type::Int);
    assert_eq!(ty_of_global(src, "b"), Type::UInt);
    assert_eq!(ty_of_global(src, "c"), Type::UInt);
    assert_eq!(ty_of_global(src, "d"), Type::Int);
}

#[test]
fn specifier_order_permutations() {
    let src = r#"
        unsigned long int x;
        long unsigned y;
    "#;
    assert_eq!(ty_of_global(src, "x"), Type::ULong);
    assert_eq!(ty_of_global(src, "y"), Type::ULong);
}

#[test]
fn arrays_and_pointers_with_kinds() {
    // unsigned char array
    let src_arr = r#"
        unsigned char buf[3];
    "#;
    assert_eq!(ty_of_global(src_arr, "buf"), Type::Array(Box::new(Type::UChar), 3));

    // pointer to unsigned short
    let src_ptr = r#"
        unsigned short *p;
    "#;
    assert_eq!(ty_of_global(src_ptr, "p"), Type::Pointer(Box::new(Type::UShort)));
}

#[test]
fn function_param_kinds() {
    let src = r#"
        int f(unsigned short a, long b, char c) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse tu");
    let f = tu.functions.iter().find(|f| f.name == "f").expect("fn f");
    let ptys: Vec<Type> = f.params.iter().map(|p| p.ty.clone()).collect();
    assert_eq!(ptys, vec![Type::UShort, Type::Long, Type::Char]);
}
