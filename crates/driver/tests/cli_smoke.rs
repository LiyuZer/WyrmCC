use assert_cmd::prelude::*;
use predicates::prelude::*;
use std::fs::File;
use std::io::Write;
use std::process::Command;
use tempfile::tempdir;

#[test]
fn help_shows_usage() {
    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.arg("--help");
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("Wyrm C Compiler"));
}

#[test]
fn preprocess_basic_macro_expansion() {
    // Create a small C file that relies on macro expansion
    let dir = tempdir().unwrap();
    let file_path = dir.path().join("test.c");
    let mut f = File::create(&file_path).unwrap();
    writeln!(f, "#define X 3").unwrap();
    writeln!(f, "int y = X;").unwrap();

    // Run: wyrmcc preprocess test.c
    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.args(["preprocess", file_path.to_string_lossy().as_ref()]);

    cmd.assert()
        .success()
        // -P suppresses linemarkers; ensure macro expanded
        .stdout(predicate::str::contains("int y = 3"));
}
