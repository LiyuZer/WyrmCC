use parse::parse_translation_unit;

#[test]
fn parse_member_access_dot_and_arrow() {
    // int main(void){ struct S{int a;} s; struct S *p=&s; s.a=1; p->a=2; return s.a + p->a; }
    let src = r#"
        int main(void) {
            struct S { int a; } s;
            struct S *p = &s;
            s.a = 1;
            p->a = 2;
            return s.a + p->a;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.functions.len(), 1);
}
