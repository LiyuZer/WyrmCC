use backend::emit_llvm_ir;
use parse::parse_translation_unit;

// Pointer codegen regression tests
// - Ensure & and * lower to ptr allocas/loads/stores
// - Ensure no unsafe constant folding is applied to pointer-typed identifiers

#[test]
fn pointers_addr_of_load() {
    // int main(){ int x=7; int *p=&x; return *p; }
    let src = r#"
        int main(void) {
            int x = 7;
            int *p = &x;
            return *p;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // x is an i32 alloca
    assert!(
        ir.contains("%x = alloca i32"),
        "missing i32 alloca for x:\n{}",
        ir
    );
    // p is a ptr alloca
    assert!(
        ir.contains("%p = alloca ptr"),
        "missing ptr alloca for p:\n{}",
        ir
    );
    // store address of x into p
    assert!(
        ir.contains("store ptr %x, ptr %p"),
        "expected store of &x into p:\n{}",
        ir
    );
    // load pointer value from p
    assert!(
        ir.contains("load ptr, ptr %p"),
        "expected load of ptr from %p before deref:\n{}",
        ir
    );
    // deref should load i32 via the loaded pointer
    assert!(
        ir.contains("load i32, ptr"),
        "expected i32 load from the dereferenced pointer:\n{}",
        ir
    );
    // Return should be an i32
    assert!(
        ir.contains("ret i32"),
        "expected integer return in IR:\n{}",
        ir
    );
}

#[test]
fn pointers_store_through() {
    // int main(){ int x=1; int *p=&x; *p=41; return x+1; }
    let src = r#"
        int main(void) {
            int x = 1;
            int *p = &x;
            *p = 41;
            return x + 1;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // p alloca as ptr, x as i32
    assert!(
        ir.contains("%x = alloca i32"),
        "missing i32 alloca for x:\n{}",
        ir
    );
    assert!(
        ir.contains("%p = alloca ptr"),
        "missing ptr alloca for p:\n{}",
        ir
    );

    // store &x into p, then store 41 through *p
    assert!(
        ir.contains("store ptr %x, ptr %p"),
        "missing store of &x into p:\n{}",
        ir
    );
    assert!(
        ir.contains("store i32 41, ptr"),
        "expected store through pointer of 41 (pattern \"store i32 41, ptr ...\"):\n{}",
        ir
    );

    // Should compute x+1 and return an i32 (value may not be folded; ensure instruction exists)
    assert!(
        ir.contains(" add i32 ") || ir.contains("add i32"),
        "expected add instruction for x+1:\n{}",
        ir
    );
    assert!(
        ir.contains("ret i32"),
        "expected integer return in IR:\n{}",
        ir
    );
}
