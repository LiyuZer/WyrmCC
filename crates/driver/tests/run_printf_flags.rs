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
fn run_printf_zero_pad_width() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("printf_width.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"int main(void) { printf("%05d\n", 7); return 0; }"#
    ).unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert().success().stdout(predicate::str::contains("00007\n"));
}

#[test]
fn run_printf_left_justify() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("printf_left.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"int main(void) { printf("%-6dX\n", 7); return 0; }"#
    ).unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert().success().stdout(predicate::str::contains("7     X\n"));
}

#[test]
fn run_printf_plus_sign() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("printf_plus.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"int main(void) { printf("%+d\n", 7); return 0; }"#
    ).unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert().success().stdout(predicate::str::contains("+7\n"));
}

#[test]
fn run_printf_space_flag() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("printf_space.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"int main(void) { printf("% d\n", 7); return 0; }"#
    ).unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert().success().stdout(predicate::str::contains(" 7\n"));
}

#[test]
fn run_printf_alternate_hex() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("printf_alt_hex.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"int main(void) { printf("%#x %#X\n", 255, 255); return 0; }"#
    ).unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert().success().stdout(predicate::str::contains("0xff 0XFF\n"));
}

#[test]
fn run_printf_string_precision() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("printf_str_prec.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"int main(void) { printf("%.3s\n", "hello"); return 0; }"#
    ).unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert().success().stdout(predicate::str::contains("hel\n"));
}

#[test]
fn run_printf_literal_percent() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("printf_percent.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"int main(void) { printf("%%\n"); return 0; }"#
    ).unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert().success().stdout(predicate::str::contains("%\n"));
}
