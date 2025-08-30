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
fn run_printf_formats_and_prints() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let c_path = dir.path().join("printf.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"int main(void) { printf("n=%d s=%s\n", 7, "ok"); return 0; }"#
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert()
        .success()
        .stdout(predicate::str::contains("n=7 s=ok\n"));
}
