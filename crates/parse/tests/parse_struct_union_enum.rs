use parse::parse_translation_unit;

#[test]
fn parse_struct_with_members_decl() {
    // struct with members used in a declaration inside a function
    // int main(void){ struct S { int a; int *b; } v; return 0; }
    let src = r#"
        int main(void) {
            struct S { int a; int *b; } v;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.functions.len(), 1);
}

#[test]
fn parse_union_with_members_decl() {
    // union with members used in a declaration inside a function
    // int main(void){ union U { int a; int *p; } u; return 0; }
    let src = r#"
        int main(void) {
            union U { int a; int *p; } u;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.functions.len(), 1);
}

#[test]
fn parse_enum_with_enumerators_decl() {
    // enum with enumerators used in a declaration inside a function
    // int main(void){ enum E { A, B, C } e; return 0; }
    let src = r#"
        int main(void) {
            enum E { A, B, C } e;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.functions.len(), 1);
}
