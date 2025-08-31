#[cfg(unix)]
use assert_cmd::prelude::*;
#[cfg(unix)]
use std::fs;
#[cfg(unix)]
use std::io::Write;
#[cfg(unix)]
use std::process::Command;
#[cfg(unix)]
use tempfile::tempdir;

#[cfg(unix)]
fn llvm_tools() -> (&'static str, &'static str) {
    ("clang-18", "llc-18")
}

// Validate integer promotions (char/short families) and UAC results at runtime.
#[cfg(unix)]
#[test]
fn promotions_and_uac_runtime() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("promos_uac.c");
    let mut f = fs::File::create(&c_path).unwrap();

    write!(
        f,
        "{}",
        r#"int main(void) {
    signed char sc = -1;
    int x = sc + 2;              // sc promotes to int -> 1
    if (x != 1) return 101;

    unsigned char uc = 250;
    int y = uc + 10;             // uc promotes to int -> 260
    if (y != 260) return 102;

    unsigned short us = 65530;
    int z = us + 10;             // us promotes to int -> 65540
    if (z != 65540) return 103;

    // Mixed long (signed) and unsigned int -> result unsigned long (32-bit here)
    long l = -1;
    unsigned int u = 1;
    unsigned long r = l + u;     // (-1 + 1) under UAC -> 0
    if (r != 0) return 104;

    return 0;
}
"#
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert().success();
}

// Validate conditional operator uses UAC for differing integer operands.
#[cfg(unix)]
#[test]
fn conditional_operator_uac_runtime() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("cond_uac.c");
    let mut f = fs::File::create(&c_path).unwrap();

    write!(
        f,
        "{}",
        r#"int main(void) {
    int i = -1;
    unsigned int uu = 1;
    unsigned int t = 1 ? i : uu; // UAC: result is unsigned, i converts to UINT_MAX
    if (t + 1 != 0) return 201;  // wrap to 0 under 32-bit arithmetic

    // Symmetric check with else branch chosen
    unsigned int t2 = 0 ? i : uu; // picks uu directly -> 1
    if (t2 != 1) return 202;

    return 0;
}
"#
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert().success();
}

#[cfg(not(unix))]
#[test]
fn promotions_and_uac_runtime_skip() {
    assert!(true);
}

#[cfg(not(unix))]
#[test]
fn conditional_operator_uac_runtime_skip() {
    assert!(true);
}
