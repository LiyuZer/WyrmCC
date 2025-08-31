use backend::emit_llvm_ir;
use parse::parse_translation_unit;

// These tests are IR-pattern checks to drive lowering for ++/-- (pre/post)
// on identifiers and pointer dereferences. They intentionally avoid over-
// specifying SSA names and only assert key operations exist.

#[test]
fn pre_inc_ident_ir_patterns() {
    // int main(void){ int x=5; ++x; return x; }
    let src = r#"
        int main(void) {
            int x = 5;
            ++x;
            return x;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Should load x, add 1, and store back to x
    assert!(
        ir.contains("%x = alloca i32"),
        "expected alloca for x, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("store i32 5, ptr %x"),
        "expected init store to x, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("load i32, ptr %x"),
        "expected a load of x before increment, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("add i32") || ir.contains("add nsw i32") || ir.contains("add nuw i32"),
        "expected an add i32 for ++x, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("store i32"),
        "expected a store after increment, IR:\n{}",
        ir
    );
}

#[test]
fn post_dec_ident_ir_patterns() {
    // int main(void){ int x=5; int y = x--; return y; }
    let src = r#"
        int main(void) {
            int x = 5;
            int y = x--;
            return y;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect a subtraction by 1 and stores to both x and y
    assert!(
        ir.contains("%x = alloca i32"),
        "expected alloca for x, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("%y = alloca i32"),
        "expected alloca for y, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("store i32 5, ptr %x"),
        "expected init of x, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("load i32, ptr %x"),
        "expected load of x before post-decrement, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("sub i32") || ir.contains("sub nsw i32") || ir.contains("sub nuw i32"),
        "expected a sub i32 for x--, IR:\n{}",
        ir
    );
    // One store should be to y (capturing original), and another updating x
    assert!(
        ir.contains("store i32"),
        "expected stores for y and updated x, IR:\n{}",
        ir
    );
}

#[test]
fn pre_inc_deref_ir_patterns() {
    // int main(void){ int x=5; int *p=&x; ++*p; return x; }
    let src = r#"
        int main(void) {
            int x = 5;
            int *p = &x;
            ++*p;
            return x;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // p should be a pointer local and be loaded to obtain the pointee address
    assert!(
        ir.contains("%p = alloca ptr"),
        "expected alloca for pointer p, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("store ptr %x, ptr %p") || ir.contains("store ptr %"),
        "expected store of &x into p, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("load ptr, ptr %p"),
        "expected load of pointer value from p, IR:\n{}",
        ir
    );

    // Then a load of the pointee, add by 1, and a store back through the loaded pointer
    assert!(
        ir.contains("load i32, ptr %"),
        "expected load of pointee (some %t SSA), IR:\n{}",
        ir
    );
    assert!(
        ir.contains("add i32") || ir.contains("add nsw i32") || ir.contains("add nuw i32"),
        "expected add i32 for ++*p, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("store i32"),
        "expected store back through pointer after increment, IR:\n{}",
        ir
    );
}
