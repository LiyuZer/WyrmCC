use assert_cmd::prelude::*;
use predicates::prelude::*;
use std::fs::File;
use std::io::Write;
use std::process::Command;
use tempfile::tempdir;

fn squash(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

#[test]
fn preprocess_internal_pp_basic() {
    let dir = tempdir().unwrap();
    let file_path = dir.path().join("test.c");
    let mut f = File::create(&file_path).unwrap();
    writeln!(f, "#define A 1").unwrap();
    writeln!(f, "int x = A;").unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.args(["preprocess", file_path.to_string_lossy().as_ref()]);

    cmd.assert()
        .success()
        .stdout(predicate::function(|out: &str| {
            squash(out).contains("intx=1;")
        }));
}

#[test]
fn preprocess_flag_define_object_macro() {
    let dir = tempdir().unwrap();
    let file_path = dir.path().join("test.c");
    let mut f = File::create(&file_path).unwrap();
    writeln!(f, "int x = FOO;").unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    // Provide -D FOO=42 on the command line
    cmd.args([
        "preprocess",
        file_path.to_string_lossy().as_ref(),
        "-D",
        "FOO=42",
    ]);

    cmd.assert()
        .success()
        .stdout(predicate::function(|out: &str| {
            squash(out).contains("intx=42;")
        }));
}

#[test]
fn preprocess_flag_ifdef_toggles() {
    let dir = tempdir().unwrap();
    let file_path = dir.path().join("test.c");
    let mut f = File::create(&file_path).unwrap();
    writeln!(f, "#ifdef FLAG").unwrap();
    writeln!(f, "int v=1;").unwrap();
    writeln!(f, "#else").unwrap();
    writeln!(f, "int v=2;").unwrap();
    writeln!(f, "#endif").unwrap();

    // With -D FLAG we should see v=1
    let mut cmd1 = Command::cargo_bin("wyrmcc").unwrap();
    cmd1.args([
        "preprocess",
        file_path.to_string_lossy().as_ref(),
        "-D",
        "FLAG=1",
    ]);
    cmd1.assert()
        .success()
        .stdout(predicate::function(|out: &str| {
            squash(out).contains("intv=1;")
        }));

    // Without -D (or with -U) we should see v=2
    let mut cmd2 = Command::cargo_bin("wyrmcc").unwrap();
    cmd2.args(["preprocess", file_path.to_string_lossy().as_ref()]);
    cmd2.assert()
        .success()
        .stdout(predicate::function(|out: &str| {
            squash(out).contains("intv=2;")
        }));
}

#[test]
fn emit_llvm_uses_internal_pp() {
    let dir = tempdir().unwrap();
    let file_path = dir.path().join("main.c");
    let mut f = File::create(&file_path).unwrap();
    writeln!(f, "#define X 7").unwrap();
    writeln!(f, "int main(void) {{ return X; }}").unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.args(["emit-llvm", file_path.to_string_lossy().as_ref()]);

    // Expect the returned IR to include a constant 7 in the ret
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("ret i32 7"));
}
