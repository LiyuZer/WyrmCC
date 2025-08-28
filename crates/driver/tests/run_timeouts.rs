use assert_cmd::prelude::*;
use predicates::str::contains;
use std::fs;
use std::io::Write;
use std::process::Command;
use tempfile::tempdir;

// Use tool names so the OS PATH resolves to the correct binaries.
fn llvm_tools() -> (&'static str, &'static str) {
    ("clang-18", "llc-18")
}

#[test]
fn run_infinite_loop_times_out() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let c_path = dir.path().join("inf.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(f, "int main(void) {{ for(;;){{}} return 0; }}").unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .env("WYRMC_TIMEOUT_SECS", "1")
        .args(["run", c_path.to_string_lossy().as_ref()]);

    // Expect a timeout-induced failure and error mention
    cmd.assert()
        .failure()
        .stderr(contains("timed out"));
}
