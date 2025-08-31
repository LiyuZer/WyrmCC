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
fn switch_basic_ir_patterns() {
    // int main(void){ int x=0; switch(x){ case 1: return 1; default: return 2; } }
    let src = r#"
        int main(void) {
            int x = 0;
            switch (x) {
                case 1: return 1;
                default: return 2;
            }
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect equality comparisons for dispatch and a conditional branch chain
    assert!(
        ir.contains("icmp eq i32"),
        "expected equality compare in switch dispatch, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("br i1 "),
        "expected conditional branch on i1 in switch dispatch, IR:\n{}",
        ir
    );

    // Expect labeled basic blocks and integer returns
    assert!(
        ir.contains("\nL") && ir.contains(":\n"),
        "expected labeled basic blocks in IR:\n{}",
        ir
    );
    assert!(
        ir.contains("ret i32 1") || ir.contains("ret i32 2"),
        "expected integer returns in IR:\n{}",
        ir
    );
}

#[test]
fn switch_fallthrough_and_break_ir_shape() {
    // int main(void){ int x=2; int y=0; switch(x){ case 1: y=1; case 2: y=2; break; default: y=3; } return y; }
    let src = r#"
        int main(void) {
            int x = 2;
            int y = 0;
            switch (x) {
                case 1:
                case 2: y = 2; break;
                default: y = 3;
            }
            return y;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Dispatch should compare and branch
    assert!(
        ir.contains("icmp eq i32"),
        "expected equality compares in dispatch, IR:\n{}",
        ir
    );
    assert!(
        ir.contains("br i1 "),
        "expected conditional branches in dispatch, IR:\n{}",
        ir
    );

    // There should be some unconditional branches for fallthrough or break to the end label
    assert!(
        ir.contains("br label %L"),
        "expected some unconditional branches to labels (fallthrough/break), IR:\n{}",
        ir
    );

    // Heuristic: ensure multiple labels exist (dispatch + case blocks + end)
    assert!(
        count_substr(&ir, "\nL") >= 3,
        "expected at least 3 labeled blocks, IR:\n{}",
        ir
    );
}
