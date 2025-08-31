use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn array_argument_decays_to_pointer() {
    // int sink(int x){ return x==0; }
    // int main(void){ int a[2]; return sink(a); }
    let src = r#"
        int sink(int x) { return x == 0; }
        int main(void) {
            int a[2];
            return sink(a);
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect decay of array identifier to pointer before call via GEP 0,0 on [2 x i32]
    assert!(
        ir.contains("getelementptr inbounds [2 x i32], ptr %a, i64 0, i64 0"),
        "expected array-to-pointer decay GEP for a before call, IR:\n{}",
        ir
    );

    // Call should be present
    assert!(
        ir.contains(" call i32 @sink("),
        "expected call to sink, IR:\n{}",
        ir
    );
}

#[test]
fn array_plus_one_gep_present() {
    // int main(void){ int a[3]; int *p = a + 1; return 0; }
    let src = r#"
        int main(void) {
            int a[3];
            int *p = a + 1;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect pointer arithmetic lowered via GEP over i32 with index 1
    assert!(
        ir.contains("getelementptr inbounds i32, ptr") && ir.contains(", i64 1"),
        "expected GEP by +1 on array decay (i32 element), IR:\n{}",
        ir
    );
}

#[test]
fn sizeof_array_vs_pointer_constant() {
    // int main(void){ int a[3]; int *p = a; return sizeof(a) - sizeof(p); }
    // sizeof(int[3]) = 12, sizeof(ptr) = 8 => result 4 on our target assumptions.
    let src = r#"
        int main(void) {
            int a[3];
            int *p = a;
            return sizeof(a) - sizeof(p);
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // We expect constant folding to yield a literal return of 4
    assert!(
        ir.contains("ret i32 4"),
        "expected ret i32 4 for sizeof(array)-sizeof(ptr), IR:\n{}",
        ir
    );
}
