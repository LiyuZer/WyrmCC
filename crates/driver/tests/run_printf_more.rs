use assert_cmd::prelude::*;
use predicates::prelude::*;
use std::fs;
use std::io::Write;
use std::process::Command;
use tempfile::tempdir;

// Use tool names so the OS PATH resolves to the correct binaries.
fn llvm_tools() -> (&'static str, &'static str) {
    ("clang-18", "llc-18")
}

#[test]
fn run_printf_multiple_integers_and_strings() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let c_path = dir.path().join("printf_more.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"int main(void) { printf("a=%d b=%d msg=%s\n", 1, 2, "ok"); return 0; }"#
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert()
        .success()
        .stdout(predicate::str::contains("a=1 b=2 msg=ok\n"));
}
