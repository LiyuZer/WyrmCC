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
fn run_agg_init_int_array_sum() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("agg_array_sum.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"int main(void) {
            int a[3] = {1,2,3};
            printf("%d\n", a[0] + a[1] + a[2]);
            return 0;
        }"#
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert().success().stdout(predicate::str::contains("6\n"));
}

#[test]
fn run_agg_init_struct_fields_sum() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("agg_struct_sum.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"int main(void) {
            struct S { int a; int b; };
            struct S s = {1, 2};
            printf("%d\n", s.a + s.b);
            return 0;
        }"#
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert().success().stdout(predicate::str::contains("3\n"));
}

#[test]
fn run_agg_init_nested_struct_array_field_sum() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("agg_nested_struct_sum.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"int main(void) {
            struct T { int a[2]; int b; };
            struct T t = { {1,2}, 3 };
            printf("%d\n", t.a[0] + t.a[1] + t.b);
            return 0;
        }"#
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert().success().stdout(predicate::str::contains("6\n"));
}

#[test]
fn run_agg_init_char_array_from_string() {
    let (clang, llc) = llvm_tools();
    let dir = tempdir().unwrap();
    let c_path = dir.path().join("agg_char_array.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"int main(void) {
            char s[3] = "hi";
            // Expect memcpy of 3 bytes (hi + NUL) and correct printf of the string
            printf("%s\n", s);
            return 0;
        }"#
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    cmd.assert().success().stdout(predicate::str::contains("hi\n"));
}
