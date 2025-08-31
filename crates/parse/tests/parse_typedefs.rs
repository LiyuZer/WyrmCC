use parse::parse_translation_unit;

#[test]
fn parse_typedef_basic() {
    // int main(void){ typedef int I; I y; return 0; }
    let src = r#"
        int main(void) {
            typedef int I;
            I y;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src);
    assert!(tu.is_ok(), "expected parse ok, got {:?}", tu);
}

#[test]
fn parse_typedef_shadowing_in_inner_block() {
    // int main(void){ typedef int I; { typedef int *I; I p; } return 0; }
    let src = r#"
        int main(void) {
            typedef int I;
            {
                typedef int *I;
                I p;
            }
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src);
    assert!(
        tu.is_ok(),
        "expected parse ok with shadowed typedef, got {:?}",
        tu
    );
}

#[test]
fn parse_typedef_with_pointer() {
    // int main(void){ typedef int *P; P p; return 0; }
    let src = r#"
        int main(void) {
            typedef int *P;
            P p;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src);
    assert!(
        tu.is_ok(),
        "expected parse ok for pointer typedef, got {:?}",
        tu
    );
}

#[test]
fn parse_sizeof_and_cast_with_typedef() {
    // int main(void){ typedef int I; return sizeof(I) + (I)5; }
    let src = r#"
        int main(void) {
            typedef int I;
            return sizeof(I) + (I)5;
        }
    "#;
    let tu = parse_translation_unit(src);
    assert!(
        tu.is_ok(),
        "expected parse ok for sizeof/cast with typedef, got {:?}",
        tu
    );
}
