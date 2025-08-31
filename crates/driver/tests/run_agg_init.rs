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
fn brace_init_array_sum() {
    // int a[5] = {1,2,3}; remaining zeros; sum should be 6
    let dir = tempdir().unwrap();
    let c = write_file(
        &dir,
        "agg1.c",
        r#"
            int printf(const char*, ...);
            int main(void) {
                int a[5] = {1,2,3};
                int s = 0;
                int i; /* C89-compatible declaration */
                for (i = 0; i < 5; i++) s += a[i];
                printf("%d\n", s);
                return 0;
            }
        "#,
    );

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.arg("run").arg(&c);
    let out = cmd.output().expect("run ok");
    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("6\n"), "stdout was: {}", stdout);
}

#[test]
fn brace_init_struct_fields() {
    // struct with {1,2} should print "1 2"
    let dir = tempdir().unwrap();
    let c = write_file(
        &dir,
        "agg2.c",
        r#"
            int printf(const char*, ...);
            struct S { int a; int b; };
            int main(void) {
                struct S s = {1, 2};
                printf("%d %d\n", s.a, s.b);
                return 0;
            }
        "#,
    );

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.arg("run").arg(&c);
    let out = cmd.output().expect("run ok");
    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("1 2\n"), "stdout was: {}", stdout);
}

#[test]
fn brace_init_nested_struct_with_array_field() {
    // struct T { int a[2]; int b; }; struct T t = {{1,2}, 3}; prints "1 2 3"
    let dir = tempdir().unwrap();
    let c = write_file(
        &dir,
        "agg3.c",
        r#"
            int printf(const char*, ...);
            struct T { int a[2]; int b; };
            int main(void) {
                struct T t = { {1,2}, 3 };
                printf("%d %d %d\n", t.a[0], t.a[1], t.b);
                return 0;
            }
        "#,
    );

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.arg("run").arg(&c);
    let out = cmd.output().expect("run ok");
    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("1 2 3\n"), "stdout was: {}", stdout);
}

#[test]
fn brace_init_char_array_from_string() {
    // char s[] = "hi"; prints hi
    let dir = tempdir().unwrap();
    let c = write_file(
        &dir,
        "agg4.c",
        r#"
            int printf(const char*, ...);
            int main(void) {
                char s[] = "hi";
                printf("%s\n", s);
                return 0;
            }
        "#,
    );

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.arg("run").arg(&c);
    let out = cmd.output().expect("run ok");
    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("hi\n"), "stdout was: {}", stdout);
}