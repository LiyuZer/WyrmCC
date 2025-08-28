use backend::emit_llvm_ir;
use parse::parse_translation_unit;

// IR-pattern checks for compound assignments (op=) on identifiers and *ptr

#[test]
fn plus_assign_ident_ir_patterns() {
    // int main(void){ int x=5; x+=3; return x; }
    let src = r#"
        int main(void) {
            int x = 5;
            x += 3;
            return x;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Alloca and init
    assert!(ir.contains("%x = alloca i32"), "expected alloca for x, IR:\n{}", ir);
    assert!(ir.contains("store i32 5, ptr %x"), "expected initial store of 5 to x, IR:\n{}", ir);

    // Load x, add 3, store back to x
    assert!(ir.contains("load i32, ptr %x"), "expected load of x before x+=3, IR:\n{}", ir);
    assert!(ir.contains("add i32") || ir.contains("add nsw i32") || ir.contains("add nuw i32"),
        "expected add i32 in x+=3, IR:\n{}", ir);
    assert!(ir.contains("store i32"), "expected store after x+=3, IR:\n{}", ir);
}

#[test]
fn and_assign_ident_ir_patterns() {
    // int main(void){ int x=6; x&=3; return x; }
    let src = r#"
        int main(void) {
            int x = 6;
            x &= 3;
            return x;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    assert!(ir.contains("%x = alloca i32"), "alloca x missing, IR:\n{}", ir);
    assert!(ir.contains("store i32 6, ptr %x"), "init x=6 missing, IR:\n{}", ir);
    assert!(ir.contains("load i32, ptr %x"), "expected load of x before &=, IR:\n{}", ir);
    assert!(ir.contains("and i32"), "expected bitwise and for &=, IR:\n{}", ir);
    assert!(ir.contains("store i32"), "expected store after &=, IR:\n{}", ir);
}

#[test]
fn mul_assign_deref_ir_patterns() {
    // int main(void){ int x=4; int *p=&x; *p*=3; return x; }
    let src = r#"
        int main(void) {
            int x = 4;
            int *p = &x;
            *p *= 3;
            return x;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // p should be a pointer local; store &x into p
    assert!(ir.contains("%p = alloca ptr"), "expected alloca for pointer p, IR:\n{}", ir);
    assert!(ir.contains("store ptr %x, ptr %p") || ir.contains("store ptr %"),
        "expected store of &x into p, IR:\n{}", ir);

    // Load pointee, multiply by 3, store back through pointer
    assert!(ir.contains("load ptr, ptr %p"), "expected load of pointer value from p, IR:\n{}", ir);
    assert!(ir.contains("load i32, ptr %"), "expected load of pointee before *=, IR:\n{}", ir);
    assert!(ir.contains("mul i32") || ir.contains("mul nsw i32") || ir.contains("mul nuw i32"),
        "expected mul i32 for *=, IR:\n{}", ir);
    assert!(ir.contains("store i32"), "expected store back through pointer after *=, IR:\n{}", ir);
}
