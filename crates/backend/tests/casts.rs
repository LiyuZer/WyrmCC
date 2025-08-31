use backend::emit_llvm_ir;
use parse::parse_translation_unit;

#[test]
fn cast_ptr_to_int_ir_patterns() {
    // int main(void){ int x=1; int *p=&x; int v=(int)p; return v; }
    let src = r#"
        int main(void) {
            int x = 1;
            int *p = &x;
            int v = (int)p;
            return v;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect a ptrtoint from ptr to i32
    assert!(
        ir.contains("ptrtoint ptr ") && ir.contains(" to i32"),
        "expected ptrtoint ptr .. to i32 in IR, got:\n{}",
        ir
    );
}

#[test]
fn cast_int_to_ptr_ir_patterns() {
    // int main(void){ int a=0; int *p=(int*)a; return p==0; }
    let src = r#"
        int main(void) {
            int a = 0;
            int *p = (int*)a;
            return p == 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect an inttoptr from i32 to ptr
    assert!(
        ir.contains("inttoptr i32"),
        "expected inttoptr i32 .. to ptr in IR, got:\n{}",
        ir
    );

    // Expect a comparison for p==0. The compare itself returns i1, but operands should be i32 or ptr.
    assert!(
        ir.contains("icmp eq i32")
            || ir.contains("icmp ne i32")
            || ir.contains("icmp eq ptr")
            || ir.contains("icmp ne ptr"),
        "expected an icmp (on i32 or ptr operands) for p==0, IR:\n{}",
        ir
    );
}

#[test]
fn cast_ptr_to_ptr_bitcast_ir_patterns() {
    // int main(void){ int x=0; int *p=&x; int **pp=(int**)&p; return p!=0; }
    let src = r#"
        int main(void) {
            int x = 0;
            int *p = &x;
            int **pp = (int**)&p;
            return p != 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect a bitcast between ptr types
    assert!(
        ir.contains("bitcast ptr "),
        "expected bitcast ptr .. to ptr in IR, got:\n{}",
        ir
    );

    // Ensure the comparison on p is present to force use of p downstream
    assert!(
        ir.contains("icmp ") || ir.contains("icmp ne"),
        "expected an icmp for p!=0, IR:\n{}",
        ir
    );
}
