use assert_cmd::prelude::*;
use std::fs::File;
use std::io::Write;
use std::process::Command;
use tempfile::tempdir;

fn tools() -> (&'static str, &'static str) { ("clang-18", "llc-18") }

#[test]
fn run_returns_6_from_mul() {
    let (clang, llc) = tools();
    let dir = tempdir().unwrap();
    let p = dir.path().join("t.c");
    let mut f = File::create(&p).unwrap();
    writeln!(f, "int main(void) {{ return 2*3; }}").unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", p.to_string_lossy().as_ref()]);
    cmd.assert().code(6);
}

#[test]
fn run_returns_7_from_sub() {
    let (clang, llc) = tools();
    let dir = tempdir().unwrap();
    let p = dir.path().join("t.c");
    let mut f = File::create(&p).unwrap();
    writeln!(f, "int main(void) {{ return 10-3; }}").unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", p.to_string_lossy().as_ref()]);
    cmd.assert().code(7);
}

#[test]
fn precedence_mul_before_add() {
    let (clang, llc) = tools();
    let dir = tempdir().unwrap();
    let p = dir.path().join("t.c");
    let mut f = File::create(&p).unwrap();
    writeln!(f, "int main(void) {{ return 2 + 3 * 4; }}").unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", p.to_string_lossy().as_ref()]);
    cmd.assert().code(14);
}

#[test]
fn unary_minus() {
    let (clang, llc) = tools();
    let dir = tempdir().unwrap();
    let p = dir.path().join("t.c");
    let mut f = File::create(&p).unwrap();
    writeln!(f, "int main(void) {{ return -5 + 12; }}").unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", p.to_string_lossy().as_ref()]);
    cmd.assert().code(7);
}
