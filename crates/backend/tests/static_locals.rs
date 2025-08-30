use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn static_local_zero_init_internal() {
    // int f(void){ static int s; return s; }
    let src = r#"
        int f(void) { static int s; return s; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect an internal global for the static local with zero init
    assert!(
        ir.contains("@__static_f_s = internal global i32 zeroinitializer")
            || ir.contains("@__static_f_s = internal global i32 0")
            || ir.contains("@__static_f_s = internal global i32 zeroinitializer,"),
        "expected internal global for static local s, IR:\n{}",
        ir
    );
    // And a load from that global in f
    assert!(
        ir.contains("define i32 @f(") && ir.contains("load i32, ptr @__static_f_s"),
        "expected load from @__static_f_s in f, IR:\n{}",
        ir
    );
}

#[test]
fn static_local_const_init_internal() {
    // int f(void){ static int s=7; return s; }
    let src = r#"
        int f(void) { static int s = 7; return s; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    assert!(
        ir.contains("@__static_f_s = internal global i32 7"),
        "expected internal global with constant init 7, IR:\n{}",
        ir
    );
}

#[test]
fn static_local_write_then_read() {
    // int f(void){ static int s; s = s + 1; return s; }
    let src = r#"
        int f(void) { static int s; s = s + 1; return s; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect both a load from and a store to the internal global
    assert!(ir.contains("@__static_f_s = internal global i32"), "expected internal global for static local s, IR:\n{}", ir);
    assert!(ir.contains("load i32, ptr @__static_f_s"), "expected load from static local global, IR:\n{}", ir);
    assert!(ir.contains("store i32") && ir.contains("@__static_f_s"), "expected store to static local global, IR:\n{}", ir);
}

#[test]
fn static_local_ptr_init_string() {
    // int f(void){ static char* p = "hi"; return (int)p; }
    let src = r#"
        int f(void) { static char* p = "hi"; return (int)p; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    assert!(
        ir.contains("@__static_f_p = internal global ptr getelementptr inbounds ([")
            && ir.contains("i8], ptr @.str."),
        "expected internal global ptr initialized from string literal, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("define i32 @f(") && ir.contains("load ptr, ptr @__static_f_p"),
        "expected load from @__static_f_p in f, IR:\n{}",
        ir
    );
}

#[test]
fn static_local_ptr_null_init() {
    // int f(void){ static char* p = 0; return p==0; }
    let src = r#"
        int f(void) { static char* p = 0; return p == 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    assert!(
        ir.contains("@__static_f_p = internal global ptr null"),
        "expected internal global ptr null initializer, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("load ptr, ptr @__static_f_p"),
        "expected function to reference @__static_f_p, IR:\n{}",
        ir
    );
}