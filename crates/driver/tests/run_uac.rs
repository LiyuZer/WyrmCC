use assert_cmd::prelude::*;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use tempfile::tempdir;

fn write_file(dir: &tempfile::TempDir, name: &str, contents: &str) -> PathBuf {
    let p = dir.path().join(name);
    fs::write(&p, contents).expect("write file ok");
    p
}

#[test]
fn uac_unsigned_wrap_prints_4294967295() {
    // unsigned wrap: (unsigned)0 - 1 == 4294967295 on 32-bit unsigned
    let dir = tempdir().unwrap();
    let c = write_file(
        &dir,
        "uac1.c",
        r#"
            int printf(const char*, ...);
            int main(void) {
                unsigned u = (unsigned)0 - 1;
                printf("%u\n", u);
                return 0;
            }
        "#,
    );

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.arg("run").arg(&c);
    let out = cmd.output().expect("run ok");
    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("4294967295\n"), "stdout was: {}", stdout);
}

#[test]
fn uac_signed_vs_unsigned_comparison() {
    // In C, -1 (int) compared with 1u (unsigned) converts -1 to unsigned -> comparison is false (0)
    let dir = tempdir().unwrap();
    let c = write_file(
        &dir,
        "uac2.c",
        r#"
            int printf(const char*, ...);
            int main(void) {
                int a = -1;
                unsigned b = 1;
                printf("%d\n", a < b);
                return 0;
            }
        "#,
    );

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.arg("run").arg(&c);
    let out = cmd.output().expect("run ok");
    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("0\n"), "stdout was: {}", stdout);
}

#[test]
fn uac_signed_vs_unsigned_right_shift() {
    // Signed right shift of -2 should be arithmetic (ashr) -> -1
    // Unsigned right shift of (unsigned)-2 should be logical (lshr) -> 2147483647 on 32-bit
    let dir = tempdir().unwrap();
    let c = write_file(
        &dir,
        "uac3.c",
        r#"
            int printf(const char*, ...);
            int main(void) {
                int si = -2;
                unsigned ui = (unsigned)-2;
                printf("%d %u\n", si >> 1, ui >> 1);
                return 0;
            }
        "#,
    );

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.arg("run").arg(&c);
    let out = cmd.output().expect("run ok");
    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("-1 2147483647\n"), "stdout was: {}", stdout);
}
