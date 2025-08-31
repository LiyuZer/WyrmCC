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
fn run_uac_signed_unsigned_comparisons() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("uac_cmp.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"int main(void) {
            int a = -1;
            unsigned int b = 1;
            // Under usual arithmetic conversions, both are converted to unsigned.
            // Thus (a < b) -> 0 and (b > a) -> 0 on 32-bit unsigned.
            printf("%d %d\n", (a < b), (b > a));
            return 0;
        }"#
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert()
        .success()
        .stdout(predicate::str::contains("0 0\n"));
}

#[test]
fn run_uac_unsigned_and_signed_shifts() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("uac_shifts.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"int main(void) {
            unsigned int ux = 0; ux = ux - 1; // UINT_MAX
            unsigned int ur = ux >> 1;        // logical shift -> 2147483647 on 32-bit unsigned
            int sx = -1;
            int sr = sx >> 1;                 // arithmetic shift -> stays -1 on two's complement
            printf("%u %d\n", ur, sr);
            return 0;
        }"#
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert()
        .success()
        .stdout(predicate::str::contains("2147483647 -1\n"));
}

#[test]
fn run_uac_promotions_char_short_to_int() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("uac_promotions.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"int main(void) {
            char c = 1;
            short s = 2;
            int x = c + s; // both promote to int
            printf("%d\n", x);
            return 0;
        }"#
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert()
        .success()
        .stdout(predicate::str::contains("3\n"));
}