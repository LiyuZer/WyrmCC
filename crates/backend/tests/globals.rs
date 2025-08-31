use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn global_int_emission() {
    // int g=41; int main(void){ return g+1; }
    let src = r#"
        int g = 41;
        int main(void) { return g + 1; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect a global integer definition
    assert!(
        ir.contains("@g = global i32 41") || ir.contains("@g = global i32 41,"),
        "expected global int definition for g=41, IR:\n{}",
        ir
    );

    // Expect a load from @g and an add
    assert!(
        ir.contains("load i32, ptr @g"),
        "expected load from global @g, IR:\n{}",
        ir
    );
    assert!(
        ir.contains(" add i32 ") || ir.contains("add i32"),
        "expected add instruction using g, IR:\n{}",
        ir
    );
}

#[test]
fn global_zero_init() {
    // int g; int main(void){ return g; }
    let src = r#"
        int g;
        int main(void) { return g; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect zeroinitialized global int
    assert!(
        ir.contains("@g = global i32 zeroinitializer") || ir.contains("@g = global i32 0"),
        "expected zeroinitialized global int g, IR:\n{}",
        ir
    );
    // And a load from @g
    assert!(
        ir.contains("load i32, ptr @g"),
        "expected load from @g in main, IR:\n{}",
        ir
    );
}

#[test]
fn global_ptr_to_string() {
    // int *p=(int*)"hi"; int main(void){ return p!=0; }
    let src = r#"
        int *p = (int*)"hi";
        int main(void) { return p != 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect a string constant and a global pointer initialized to it
    assert!(
        ir.contains("@.str") || ir.contains("@str"),
        "expected emitted string constant, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("@p = global ptr"),
        "expected global pointer @p, IR:\n{}",
        ir
    );

    // Some backends bitcast or use gep; be flexible but ensure the compare exists
    assert!(
        ir.contains("icmp ") && (ir.contains(" ne ") || ir.contains(" eq ")),
        "expected icmp using p in main, IR:\n{}",
        ir
    );
}
