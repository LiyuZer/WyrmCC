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
fn run_if_else_returns_2() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let c_path = dir.path().join("if_else.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(f, "int main(void) {{ if(1) return 2; else return 3; }}").unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    // Expect the process to exit with code 2
    cmd.assert().code(2);
}

#[test]
fn run_while_sum_returns_10() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let c_path = dir.path().join("while_sum.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(f, "int main(void) {{ int i=0; int s=0; while(i<5){{ s=s+i; i=i+1; }} return s; }}").unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    // s = 0+1+2+3+4 = 10
    cmd.assert().code(10);
}
