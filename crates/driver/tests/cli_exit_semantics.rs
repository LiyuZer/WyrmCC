use assert_cmd::prelude::*;
use std::fs;
use std::io::Write;
use std::process::Command;
use tempfile::tempdir;

// Use tool names so the OS PATH resolves to the correct binaries.
fn llvm_tools() -> (&'static str, &'static str) {
    ("clang-18", "llc-18")
}

#[test]
fn cli_run_propagates_exit_code() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let c_path = dir.path().join("ret37.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(f, "int main(void) {{ return 37; }}").unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    // The child process (wyrmcc) should exit with code 37 and not affect the test harness.
    cmd.assert().code(37);
}

#[test]
fn cli_tokens_still_works_after_run() {
    // Sanity check that we can still invoke another subcommand immediately after.
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("tiny.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(f, "int main(void) {{ return 0; }}").unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.args(["tokens", c_path.to_string_lossy().as_ref()]);

    // We only assert it runs successfully; output content can vary.
    cmd.assert().success();
}
