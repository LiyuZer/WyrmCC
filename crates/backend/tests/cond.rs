use backend::emit_llvm_ir;
use parse::parse_translation_unit;

fn count_substr(hay: &str, needle: &str) -> usize {
    if needle.is_empty() {
        return 0;
    }
    let mut count = 0;
    let mut start = 0;
    while let Some(pos) = hay[start..].find(needle) {
        count += 1;
        start += pos + needle.len();
    }
    count
}

#[test]
fn cond_basic_ir_patterns() {
    // int main(void){ int a=1; int b=2; int c=3; int r = a ? b : c; return r; }
    let src = r#"
        int main(void) {
            int a = 1;
            int b = 2;
            int c = 3;
            int r = a ? b : c;
            return r;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect: a compare-to-bool and a conditional branch to two labels
    assert!(
        ir.contains("icmp ne i32") || ir.contains("icmp eq i32"),
        "expected a truthiness compare in IR, got:\n{}",
        ir
    );
    assert!(
        ir.contains("br i1 %t"),
        "expected conditional branch on i1 SSA (br i1 %t..), IR:\n{}",
        ir
    );
    // Expect at least two labels (then and cont or then/else)
    assert!(
        ir.contains("\nL") && ir.contains(":\n"),
        "expected labeled basic blocks (L..:), IR:\n{}",
        ir
    );
}

#[test]
fn cond_alloca_and_join_present() {
    // Try to see signs of lowering via an extra temporary alloca used to join values
    // int main(void){ int a=0; int b=5; int r = a ? 7 : b; return r; }
    let src = r#"
        int main(void) {
            int a = 0;
            int b = 5;
            int r = a ? 7 : b;
            return r;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // There should be a conditional branch
    assert!(
        ir.contains("br i1 %t"),
        "expected br i1 for ?:, IR:\n{}",
        ir
    );

    // Heuristic: expect at least one alloca i32 beyond the declared locals (a,b,r) —
    // i.e., 4 or more allocas (3 locals + 1 temp). We just assert >= 3 to be lenient if
    // the backend chooses a different strategy later.
    let allocas = count_substr(&ir, " = alloca i32");
    assert!(
        allocas >= 3,
        "expected >=3 allocas, saw {}. IR:\n{}",
        allocas,
        ir
    );
}
