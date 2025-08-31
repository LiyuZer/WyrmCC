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
fn run_char_ptr_diff_counts_elements() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("char_ptr_diff.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"
        int main(void) {
            char a[10];
            char *p1 = &a[2];
            char *p2 = &a[7];
            // Expect 5 elements difference
            printf("%d\n", p2 - p1);
            return 0;
        }
        "#
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert()
        .success()
        .stdout(predicate::str::contains("5\n"));
}

#[test]
fn run_short_ptr_diff_counts_elements() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("short_ptr_diff.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"
        int main(void) {
            short a[10];
            short *p1 = &a[2];
            short *p2 = &a[7];
            // Expect 5 elements difference (scales by sizeof(short)=2)
            printf("%d\n", p2 - p1);
            return 0;
        }
        "#
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert()
        .success()
        .stdout(predicate::str::contains("5\n"));
}

#[test]
fn run_short_add_then_compare() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("short_add_then_compare.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"
        int main(void) {
            short a[3];
            short *p = a;
            p = p + 2; // advance by 2 elements
            // Expect equality with &a[2]
            printf("%d\n", (p == &a[2]));
            return 0;
        }
        "#
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert()
        .success()
        .stdout(predicate::str::contains("1\n"));
}
