#[cfg(unix)]
use assert_cmd::prelude::*;
#[cfg(unix)]
use predicates::str::contains;
#[cfg(unix)]
use std::fs;
#[cfg(unix)]
use std::io::Write;
#[cfg(unix)]
use std::process::Command;
#[cfg(unix)]
use tempfile::tempdir;

// Use tool names so the OS PATH resolves to the correct binaries.
#[cfg(unix)]
fn llvm_tools() -> (&'static str, &'static str) {
    ("clang-18", "llc-18")
}

// This test exercises usual arithmetic conversions between signed int and unsigned int,
// and conditional-operator (?:) result typing in a minimal form the current compiler supports.
// It will serve as a baseline before we broaden to char/short/long and full UAC.
#[cfg(unix)]
#[test]
fn run_uac_int_vs_uint_and_conditional() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let c_path = dir.path().join("uac.c");
    let mut f = fs::File::create(&c_path).unwrap();

    // In C, for int vs unsigned int in relational operators, both are converted to unsigned int.
    // Let a = -1 (int), b = 1u (unsigned). Then:
    //   a < b => false (since a converts to a big unsigned), so (a < b) ? a : b yields b => 1u
    //   a > b => true, so (a > b) ? a : b yields a converted to unsigned => 0xFFFFFFFFu
    // We validate these via returns; if behavior deviates, program returns nonzero.
    writeln!(
        f,
        "{}",
        r#"int main(void) {
    int a = -1;
    unsigned int b = 1u;

    unsigned int c = (a < b) ? a : b; // expect 1u
    if (c != 1u) return 11;

    unsigned int d = (a > b) ? a : b; // expect 0xFFFFFFFFu
    if ((d + 1u) != 0u) return 12; // wrap-around check implies d == 0xFFFFFFFF

    // Also ensure assigning signed -1 to unsigned via ?: path follows conversion
    unsigned int e = (a ? a : b); // a is nonzero => pick a => converted to unsigned
    if ((e + 1u) != 0u) return 13;

    return 0;
}"
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    // Expect success (exit code 0) if conversions and ?: typing behave as C89 for int vs unsigned int
    cmd.assert().success();
}

// On non-Unix platforms, skip (runner expectations and toolchain names differ)
#[cfg(not(unix))]
#[test]
fn run_uac_int_vs_uint_and_conditional_skip() { assert!(true); }
