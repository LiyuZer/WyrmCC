use assert_cmd::prelude::*;
use std::fs;
use std::io::Write;
use std::process::Command;
use tempfile::tempdir;

fn llvm_tools() -> (&'static str, &'static str) {
    ("clang-18", "llc-18")
}

#[test]
fn link_two_objects_returns_42() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let tu1 = dir.path().join("tu1.c");
    let tu2 = dir.path().join("tu2.c");

    // TU1: definition used by TU2
    let mut f1 = fs::File::create(&tu1).unwrap();
    writeln!(f1, "int add42(int x) {{ return x + 42; }}").unwrap();

    // TU2: references symbol from TU1
    let mut f2 = fs::File::create(&tu2).unwrap();
    writeln!(f2, "extern int add42(int x); int main(void) {{ return add42(0); }}").unwrap();

    // Compile each TU to an object using wyrmcc -c
    let o1 = dir.path().join("tu1.o");
    let mut c1 = Command::cargo_bin("wyrmcc").unwrap();
    c1.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["build", "-c", "-o", o1.to_string_lossy().as_ref(), tu1.to_string_lossy().as_ref()]);
    c1.assert().success();

    let o2 = dir.path().join("tu2.o");
    let mut c2 = Command::cargo_bin("wyrmcc").unwrap();
    c2.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["build", "-c", "-o", o2.to_string_lossy().as_ref(), tu2.to_string_lossy().as_ref()]);
    c2.assert().success();

    // Link with clang
    let exe = dir.path().join("a.out");
    let status = Command::new(clang)
        .args([
            "-no-pie",
            o1.to_string_lossy().as_ref(),
            o2.to_string_lossy().as_ref(),
            "-o",
            exe.to_string_lossy().as_ref(),
        ])
        .status()
        .expect("failed to link with clang");
    assert!(status.success(), "clang link failed: {status}");

    // Run and assert exit code 42
    let code = Command::new(&exe)
        .status()
        .expect("failed to run a.out")
        .code()
        .unwrap_or(1);
    assert_eq!(code, 42, "program exit code was {code}, expected 42");
}

#[test]
fn link_extern_global_across_tus() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let tu1 = dir.path().join("gdef.c");
    let tu2 = dir.path().join("useg.c");

    // TU1: define a global
    let mut f1 = fs::File::create(&tu1).unwrap();
    writeln!(f1, "int g = 7; int helper(void) {{ return 0; }}").unwrap();

    // TU2: declare extern and return its value in main
    let mut f2 = fs::File::create(&tu2).unwrap();
    writeln!(f2, "extern int g; int main(void) {{ return g; }}").unwrap();

    // Compile to objects
    let o1 = dir.path().join("gdef.o");
    let mut c1 = Command::cargo_bin("wyrmcc").unwrap();
    c1.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["build", "-c", "-o", o1.to_string_lossy().as_ref(), tu1.to_string_lossy().as_ref()]);
    c1.assert().success();

    let o2 = dir.path().join("useg.o");
    let mut c2 = Command::cargo_bin("wyrmcc").unwrap();
    c2.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["build", "-c", "-o", o2.to_string_lossy().as_ref(), tu2.to_string_lossy().as_ref()]);
    c2.assert().success();

    // Link with clang
    let exe = dir.path().join("a.out");
    let status = Command::new(clang)
        .args([
            "-no-pie",
            o1.to_string_lossy().as_ref(),
            o2.to_string_lossy().as_ref(),
            "-o",
            exe.to_string_lossy().as_ref(),
        ])
        .status()
        .expect("failed to link with clang");
    assert!(status.success(), "clang link failed: {status}");

    // Run and assert exit code 7
    let code = Command::new(&exe)
        .status()
        .expect("failed to run a.out")
        .code()
        .unwrap_or(1);
    assert_eq!(code, 7, "program exit code was {code}, expected 7");
}