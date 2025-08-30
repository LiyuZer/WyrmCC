use sema::check_translation_unit;
use parse::parse_translation_unit;

#[test]
fn extern_decl_only_ok() {
    let src = r#"
        extern int g;
        int main(void){ return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    check_translation_unit(&tu).expect("extern decl only should be ok");
}

#[test]
fn extern_with_init_err() {
    let src = r#"
        extern int g = 1;
        int main(void){ return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let err = check_translation_unit(&tu).expect_err("extern with init should error");
    let msg = format!("{}", err);
    assert!(msg.contains("extern global") && msg.contains("g"), "unexpected error: {}", msg);
}

#[test]
fn multiple_tentatives_ok() {
    let src = r#"
        int g; int g;
        int main(void){ return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    check_translation_unit(&tu).expect("multiple tentatives ok");
}

#[test]
fn tentative_plus_def_ok() {
    let src = r#"
        int g; int g = 3;
        int main(void){ return g; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    check_translation_unit(&tu).expect("tentative + def ok");
}

#[test]
fn duplicate_defs_err() {
    let src = r#"
        int g = 1; int g = 2;
        int main(void){ return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let err = check_translation_unit(&tu).expect_err("duplicate defs should error");
    let msg = format!("{}", err);
    assert!(msg.contains("duplicate global definition"), "unexpected error: {}", msg);
}
