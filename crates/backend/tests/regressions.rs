use backend::emit_llvm_ir;
use parse::parse_translation_unit;

// A1: Pointer aliasing should invalidate integer const cache so later loads are not
// folded into constants.
#[test]
fn pointer_aliasing_invalidates_consts() {
    // int main(void){ int x=5; int *p=&x; *p=7; return x; }
    let src = r#"
        int main(void) {
            int x = 5;
            int *p = &x;
            *p = 7;
            return x;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Sanity: locals and initializations
    assert!(ir.contains("%x = alloca i32"), "expected alloca for x, IR:\n{}", ir);
    assert!(ir.contains("%p = alloca ptr"), "expected alloca for p, IR:\n{}", ir);
    assert!(ir.contains("store i32 5, ptr %x"), "expected init store to x, IR:\n{}", ir);
    assert!(
        ir.contains("store ptr %x, ptr %p") || ir.contains("store ptr %"),
        "expected store of &x into p, IR:\n{}",
        ir
    );

    // Store through pointer should appear and be via some %t SSA loaded from %p
    assert!(
        ir.contains("store i32 7, ptr %"),
        "expected store through pointer of 7, IR:\n{}",
        ir
    );

    // Return should load x, not fold to a literal constant
    assert!(ir.contains("load i32, ptr %x"), "expected final load of x, IR:\n{}", ir);
    assert!(
        ir.contains("ret i32 %"),
        "expected ret of SSA value (not a constant), IR:\n{}",
        ir
    );
}

// A1: Nested loops should not allow unsafe constant folding of loop-carried vars.
#[test]
fn nested_loops_no_const_folding() {
    // int main(void){
    //   int i=0, j, sum=0;
    //   while(i<3){
    //     j=0;
    //     while(j<2){ sum = sum + i + j; j = j + 1; }
    //     i = i + 1;
    //   }
    //   return sum;
    // }
    let src = r#"
        int main(void) {
            int i = 0;
            int j;
            int sum = 0;
            while (i < 3) {
                j = 0;
                while (j < 2) {
                    sum = sum + i + j;
                    j = j + 1;
                }
                i = i + 1;
            }
            return sum;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Heuristic IR checks: we should see loads of i and j (not constants) used in compares
    assert!(ir.contains("%i = alloca i32") && ir.contains("%j = alloca i32"), "expected allocas for i and j, IR:\n{}", ir);
    assert!(ir.contains("load i32, ptr %i"), "expected a load of i in loop, IR:\n{}", ir);
    assert!(ir.contains("load i32, ptr %j"), "expected a load of j in inner loop, IR:\n{}", ir);
    // Some compare should exist (slt / sle etc.)
    assert!(ir.contains("icmp") && (ir.contains("slt") || ir.contains("sle") || ir.contains("sgt") || ir.contains("sge")),
            "expected icmp in loop condition(s), IR:\n{}", ir);
}

// A1: String literal lowering: check GEP form and that escapes are hex-encoded correctly.
#[test]
fn string_gep_and_escapes() {
    // int main(void){ puts("a\"b\\c\n"); return 0; }
    let src = r#"
        int main(void) {
            puts("a\"b\\c\n");
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Decl for puts, GEP for string, and global constant with escapes
    assert!(ir.contains("declare i32 @puts(ptr)"), "expected puts declaration, IR:\n{}", ir);

    // There should be a global constant with hex escapes for '"' (0x22), '\\' (0x5C), and '\n' (0x0A), plus NUL (0x00)
    assert!(ir.contains("private unnamed_addr constant ["), "expected a private unnamed_addr string constant, IR:\n{}", ir);
    assert!(ir.contains(" c\""), "expected c\"...\" form for constant bytes, IR:\n{}", ir);
    assert!(ir.contains("\\22"), "expected hex escape for quote (\\22), IR:\n{}", ir);
    assert!(ir.contains("\\5C"), "expected hex escape for backslash (\\5C), IR:\n{}", ir);
    assert!(ir.contains("\\0A"), "expected hex escape for newline (\\0A), IR:\n{}", ir);
    assert!(ir.contains("\\00"), "expected NUL terminator (\\00), IR:\n{}", ir);

    // Check GEP uses [N x i8], ptr @.str.*, i64 0, i64 0
    assert!(ir.contains("getelementptr inbounds ["), "expected GEP with array element type, IR:\n{}", ir);
    assert!(ir.contains("ptr @.str."), "expected GEP to reference a @.str.* global, IR:\n{}", ir);
    assert!(ir.contains(", i64 0, i64 0"), "expected GEP indices i64 0, i64 0, IR:\n{}", ir);
}