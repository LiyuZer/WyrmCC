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
fn do_while_sum_ir_patterns() {
    // int main(void){ int i=0; int s=0; do { s=s+i; i=i+1; } while(i<5); return s; }
    let src = r#"
        int main(void) {
            int i = 0; int s = 0;
            do {
                s = s + i;
                i = i + 1;
            } while (i < 5);
            return s;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect dynamic comparison for i < 5
    assert!(
        ir.contains("icmp slt i32"),
        "expected signed less-than compare for i<5, IR:\n{}",
        ir
    );

    // The to_bool lowering should feed a conditional branch (br i1 %t, ...)
    assert!(
        ir.contains("br i1 %t"),
        "expected conditional branch on i1 temporary, IR:\n{}",
        ir
    );

    // At-least-once loop shape: an initial jump to the body and a backedge.
    let br_to_label = count_substr(&ir, "br label %L");
    assert!(br_to_label >= 2, "expected at least two unconditional branches to labels (entry->body and backedge), IR:\n{}", ir);

    // Sanity: arithmetic happens inside the loop
    assert!(
        ir.contains(" add i32 ") || ir.contains("add i32"),
        "expected add instruction for s+i and/or i+1, IR:\n{}",
        ir
    );

    // Return should be i32
    assert!(
        ir.contains("ret i32"),
        "expected integer return in IR:\n{}",
        ir
    );
}
