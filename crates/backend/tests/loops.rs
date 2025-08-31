use backend::emit_llvm_ir;
use parse::parse_translation_unit;

// These tests ensure we do not constant-fold identifiers inside loops.
// Regressions here can lead to infinite loops at runtime.

#[test]
fn while_sum_ir_not_constant_folded() {
    // int main(void) { int i=0; int s=0; while(i<5){ s=s+i; i=i+1; } return s; }
    let src = r#"
        int main(void) {
            int i=0; int s=0;
            while(i<5){ s=s+i; i=i+1; }
            return s;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Condition should compare i against 5 dynamically (no constant 1 truthiness)
    assert!(
        ir.contains("icmp slt i32"),
        "expected a signed less-than compare in IR to check i<5, got:\n{}",
        ir
    );

    // After comparison (which yields i32 via zext), to_bool should compare a %t SSA against 0,
    // not a literal like `icmp ne i32 1, 0`.
    assert!(
        ir.contains("icmp ne i32 %t"),
        "expected to_bool against an SSA temporary (not a literal), got:\n{}",
        ir
    );
    assert!(
        !ir.contains("icmp ne i32 1, 0"),
        "loop condition incorrectly constant-folded to literal 1, IR:\n{}",
        ir
    );

    // The loop should have a backedge
    assert!(
        ir.contains("br label %L"),
        "expected backedge/unconditional branch to a label:\n{}",
        ir
    );

    // And we should load i within the loop at least once.
    assert!(
        ir.contains("load i32, ptr %i"),
        "expected loads of i from its alloca inside loop, IR:\n{}",
        ir
    );
}

#[test]
fn for_sum_ir_not_constant_folded() {
    // int main(void) { int s=0; int i; for(i=0; i<5; i=i+1){ s = s + i; } return s; }
    let src = r#"
        int main(void) {
            int s=0; int i;
            for(i=0; i<5; i=i+1) { s = s + i; }
            return s;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Condition compare should exist and be dynamic
    assert!(
        ir.contains("icmp slt i32"),
        "expected a signed less-than compare in IR to check i<5, got:\n{}",
        ir
    );

    // Ensure to_bool uses an SSA temporary
    assert!(
        ir.contains("icmp ne i32 %t"),
        "expected to_bool against an SSA temporary (not a literal), got:\n{}",
        ir
    );
    assert!(
        !ir.contains("icmp ne i32 1, 0"),
        "for-loop condition incorrectly constant-folded to literal 1, IR:\n{}",
        ir
    );

    // Backedge and loads
    assert!(
        ir.contains("br label %L"),
        "expected backedge/unconditional branch to a label:\n{}",
        ir
    );
    assert!(
        ir.contains("load i32, ptr %i"),
        "expected loads of i from its alloca inside loop, IR:\n{}",
        ir
    );
}
