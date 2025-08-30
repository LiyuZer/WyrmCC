use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn emit_single_for_tentatives() {
    // Two tentative declarations must produce exactly one global definition with zero init.
    let src = r#"
        int g; int g;
        int main(void){ return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    let cnt = ir.matches("@g = ").count();
    assert_eq!(cnt, 1, "expected exactly one global emission for g, IR:\n{}", ir);
    assert!(
        ir.contains("@g = global i32 zeroinitializer")
            || ir.contains("@g = global i32 0")
            || ir.contains("@g = global i32 zeroinitializer,"),
        "expected zero-initialized global for tentative g, IR:\n{}",
        ir
    );
}

#[test]
fn prefer_definition_over_extern() {
    // Definition with initializer should win over extern decl, emitting exactly one non-external global.
    let src = r#"
        extern int g;
        int g = 3;
        int main(void){ return g; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    let cnt = ir.matches("@g = ").count();
    assert_eq!(cnt, 1, "expected exactly one @g emission, IR:\n{}", ir);
    assert!(ir.contains("@g = global i32 3"), "expected concrete definition with 3, IR:\n{}", ir);
    assert!(!ir.contains("@g = external global i32"), "should not emit external for g when definition exists, IR:\n{}", ir);
}

#[test]
fn extern_only_emits_external() {
    // Only an extern declaration should emit an external global and no definition.
    let src = r#"
        extern int g;
        int main(void){ return g; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    let cnt = ir.matches("@g = ").count();
    assert_eq!(cnt, 1, "expected exactly one @g emission, IR:\n{}", ir);
    assert!(ir.contains("@g = external global i32"), "expected external global for g, IR:\n{}", ir);
    assert!(!ir.contains("@g = global i32 "), "should not emit non-external definition for g, IR:\n{}", ir);
}
