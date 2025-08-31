use parse::parse_translation_unit;

#[test]
fn parse_index_basic() {
    let src = r#"
        int main(void) {
            int i;
            int *p;
            return p[i];
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let dump = format!("{:#?}", tu);
    assert!(
        dump.contains("Index"),
        "AST should contain Index node, got:\n{}",
        dump
    );
}

#[test]
fn parse_index_with_expression() {
    let src = r#"
        int main(void) {
            int i;
            int *p;
            return p[i+1];
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let dump = format!("{:#?}", tu);
    assert!(
        dump.contains("Index"),
        "AST should contain Index node for p[i+1], got:\n{}",
        dump
    );
}
