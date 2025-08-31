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

// Validate sizeof for core C89 integer types under current target assumptions.
// Assumptions (consistent with existing tests):
// - char = 1, signed char = 1, unsigned char = 1
// - short = 2, unsigned short = 2
// - int = 4, unsigned int = 4
// - long = 4, unsigned long = 4  (LLP64-like model in this project)
// - void* = 8
#[cfg(unix)]
#[test]
fn sizeof_integers_and_pointers() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("sizeof_ints.c");
    let mut f = fs::File::create(&c_path).unwrap();

    writeln!(
        f,
        r#"int main(void) {{
    if (sizeof(char) != 1) return 101;
    if (sizeof(signed char) != 1) return 102;
    if (sizeof(unsigned char) != 1) return 103;

    if (sizeof(short) != 2) return 201;
    if (sizeof(unsigned short) != 2) return 202;

    if (sizeof(int) != 4) return 301;
    if (sizeof(unsigned int) != 4) return 302;

    if (sizeof(long) != 4) return 401;
    if (sizeof(unsigned long) != 4) return 402;

    if (sizeof(void*) != 8) return 501;

    return 0;
}}"#
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
fn sizeof_integers_and_pointers_skip() {
    assert!(true);
}
