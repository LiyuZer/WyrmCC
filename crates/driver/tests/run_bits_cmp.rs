use assert_cmd::prelude::*;
use std::fs::File;
use std::io::Write;
use std::process::Command;
use tempfile::tempdir;

fn tools() -> (&'static str, &'static str) {
    ("clang-18", "llc-18")
}

#[test]
fn shifts_and_bitwise() {
    let (clang, llc) = tools();
    let dir = tempdir().unwrap();
    let p = dir.path().join("t.c");
    let mut f = File::create(&p).unwrap();
    // (1<<5)=32, (32>>2)=8, (6&3)=2, (6|1)=7, (6^2)=4  => sum=53
    writeln!(
        f,
        "int main(void) {{ return (1<<5) + (32>>2) + (6&3) + (6|1) + (6^2); }}"
    )
    .unwrap();
    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", p.to_string_lossy().as_ref()]);
    cmd.assert().code(53);
}

#[test]
fn bitnot_combo_returns_zero() {
    let (clang, llc) = tools();
    let dir = tempdir().unwrap();
    let p = dir.path().join("t.c");
    let mut f = File::create(&p).unwrap();
    // ~5 == -6, so -6 + 6 == 0
    writeln!(f, "int main(void) {{ return (~5) + 6; }}").unwrap();
    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", p.to_string_lossy().as_ref()]);
    cmd.assert().code(0);
}

#[test]
fn comparisons_return_0_or_1() {
    let (clang, llc) = tools();
    let dir = tempdir().unwrap();
    let p = dir.path().join("t.c");
    let mut f = File::create(&p).unwrap();
    // 3<4=1, 5==5=1, 5!=5=0, 10>=7=1, 2>7=0 -> sum = 3
    writeln!(
        f,
        "int main(void) {{ return (3<4) + (5==5) + (5!=5) + (10>=7) + (2>7); }}"
    )
    .unwrap();
    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", p.to_string_lossy().as_ref()]);
    cmd.assert().code(3);
}

#[test]
fn precedence_mixed_bitwise_and_cmp() {
    let (clang, llc) = tools();
    let dir = tempdir().unwrap();
    let p = dir.path().join("t.c");
    let mut f = File::create(&p).unwrap();
    // (1|2)==3 -> 1; (4&1)==1 -> 0; (8^8)==0 -> 1 when ==0; sum = 2
    writeln!(
        f,
        "int main(void) {{ return ((1|2)==3) + ((4&1)==1) + ((8^8)==0); }}"
    )
    .unwrap();
    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", p.to_string_lossy().as_ref()]);
    cmd.assert().code(2);
}
