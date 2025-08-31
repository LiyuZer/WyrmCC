use assert_cmd::prelude::*;
use predicates::prelude::*;
use std::fs::File;
use std::io::Write;
use std::process::Command;
use tempfile::tempdir;

#[test]
fn emit_llvm_basic_return_0() {
    let dir = tempdir().unwrap();
    let file_path = dir.path().join("t.c");
    let mut f = File::create(&file_path).unwrap();
    writeln!(f, "int main(void) {{ return 0; }}").unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.args(["emit-llvm", file_path.to_string_lossy().as_ref()]);
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("define i32 @main"))
        .stdout(predicate::str::contains("ret i32 0"));
}

#[test]
fn emit_llvm_decl_and_return_ident() {
    let dir = tempdir().unwrap();
    let file_path = dir.path().join("t2.c");
    let mut f = File::create(&file_path).unwrap();
    writeln!(f, "int main(void) {{ int y = 3 + 4; return y; }}").unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.args(["emit-llvm", file_path.to_string_lossy().as_ref()]);
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("define i32 @main"))
        .stdout(predicate::str::contains("ret i32 7"));
}
