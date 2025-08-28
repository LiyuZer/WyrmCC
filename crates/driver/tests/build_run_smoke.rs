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
fn build_compile_only_object() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let c_path = dir.path().join("ret7.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(f, "int main(void) {{ return 7; }}").unwrap();

    let out_o = dir.path().join("out.o");

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args([
            "build",
            "-c",
            "-o",
            out_o.to_string_lossy().as_ref(),
            c_path.to_string_lossy().as_ref(),
        ]);

    cmd.assert().success();

    assert!(out_o.is_file(), "object file not created");
    let meta = fs::metadata(&out_o).unwrap();
    assert!(meta.len() > 0, "object file is empty");
}

#[test]
fn build_emit_assembly() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let c_path = dir.path().join("ret0.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(f, "int main(void) {{ return 0; }}").unwrap();

    let out_s = dir.path().join("out.s");

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args([
            "build",
            "-S",
            "-o",
            out_s.to_string_lossy().as_ref(),
            c_path.to_string_lossy().as_ref(),
        ]);

    cmd.assert().success();

    assert!(out_s.is_file(), "assembly file not created");
    let meta = fs::metadata(&out_s).unwrap();
    assert!(meta.len() > 0, "assembly file is empty");
}

#[test]
fn run_returns_exit_code() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let c_path = dir.path().join("ret42.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(f, "int main(void) {{ return 42; }}").unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    // Expect the process to exit with code 42
    cmd.assert().code(42);
}