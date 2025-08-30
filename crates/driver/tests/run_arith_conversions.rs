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
fn run_shr_negative_is_arithmetic() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let c_path = dir.path().join("shr_neg.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        r#"int main(void) {{ int x = -2; return (x >> 1) == -1; }}"#
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    // Expect arithmetic shift right semantics for >> on signed int (-2 >> 1 == -1)
    cmd.assert().code(1);
}

#[test]
fn run_mod_negative_semantics() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let c_path = dir.path().join("mod_neg.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        r#"int main(void) {{ return ((-7 / 3) == -2) && ((-7 % 3) == -1); }}"#
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    // Expect signed division and remainder semantics: -7/3=-2 and -7%3=-1
    cmd.assert().code(1);
}

#[test]
fn run_ptr_index_negative() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let c_path = dir.path().join("ptr_index_neg.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        r#"int main(void) {{ int a[1]; int *p = a + 1; *(p - 1) = 42; return a[0]; }}"#
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    // Ensure negative pointer index (p-1) addresses a[0]
    cmd.assert().code(42);
}
