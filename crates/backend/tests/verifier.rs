use backend::verify_llvm_text;

#[test]
fn ok_simple_function() {
    let ir = r#"; ModuleID = 'm'
define i32 @main() {
entry:
  br label %L1
L1:
  br label %L2
L2:
  ret i32 0
}
"#;
    assert!(verify_llvm_text(ir).is_ok());
}

#[test]
fn err_missing_terminator_before_next_label() {
    let ir = r#"; ModuleID = 'm'
define i32 @f() {
entry:
  %t1 = add i32 1, 2
L1:
  ret i32 0
}
"#;
    let e = verify_llvm_text(ir).unwrap_err();
    assert!(e.to_string().contains("missing terminator"), "unexpected error: {e}");
}

#[test]
fn err_instruction_after_terminator() {
    let ir = r#"; ModuleID = 'm'
define i32 @f() {
entry:
  br label %L1
  %t1 = add i32 1, 2
L1:
  ret i32 0
}
"#;
    let e = verify_llvm_text(ir).unwrap_err();
    assert!(e.to_string().contains("instruction after terminator"), "unexpected error: {e}");
}

#[test]
fn err_branch_to_undefined_label() {
    let ir = r#"; ModuleID = 'm'
define i32 @f() {
entry:
  br label %NOPE
}
"#;
    let e = verify_llvm_text(ir).unwrap_err();
    assert!(e.to_string().contains("undefined label"), "unexpected error: {e}");
}

#[test]
fn err_multiple_terminators_in_block() {
    let ir = r#"; ModuleID = 'm'
define i32 @f() {
entry:
  br label %L1
  br label %L2
L1:
  ret i32 0
L2:
  ret i32 0
}
"#;
    let e = verify_llvm_text(ir).unwrap_err();
    assert!(e.to_string().contains("multiple terminators"), "unexpected error: {e}");
}
