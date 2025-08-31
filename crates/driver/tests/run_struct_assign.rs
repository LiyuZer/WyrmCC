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
fn run_struct_assign_direct_copies_values() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let c_path = dir.path().join("struct_assign_direct.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"
            #include <stdio.h>
            struct S { int a; int b; };
            int main(void) {
                struct S s1; s1.a = 1; s1.b = 2;
                struct S s2; s2 = s1;
                printf("%d %d\n", s2.a, s2.b);
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
        .stdout(predicate::str::contains("1 2\n"));
}

#[test]
fn run_struct_assign_through_pointer_copies_values() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let c_path = dir.path().join("struct_assign_ptr.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"
            #include <stdio.h>
            struct S { int a; int b; };
            int main(void) {
                struct S s1; struct S s2; struct S *p = &s1;
                s2.a = 3; s2.b = 4;
                *p = s2;
                printf("%d %d\n", s1.a, s1.b);
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
        .stdout(predicate::str::contains("3 4\n"));
}
