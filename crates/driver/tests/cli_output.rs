use assert_cmd::prelude::*;
use predicates::prelude::*;
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use tempfile::tempdir;

// Helper to write a file in a tempdir
fn write_file(dir: &tempfile::TempDir, name: &str, contents: &str) -> PathBuf {
    let p = dir.path().join(name);
    fs::write(&p, contents).expect("write file ok");
    p
}

#[test]
fn emit_ir_with_emit_llvm_subcommand() {
    // Create simple source
    let dir = tempdir().unwrap();
    let main_c = write_file(
        &dir,
        "main.c",
        r#"
            int main(void) { return 0; }
        "#,
    );

    // wyrmcc emit-llvm main.c -> stdout contains ModuleID or define @main
    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.arg("emit-llvm").arg(&main_c);
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("; ModuleID =").or(predicate::str::contains("define i32 @main")));
}

#[test]
fn assemble_with_S_and_o() {
    let dir = tempdir().unwrap();
    let main_c = write_file(
        &dir,
        "main.c",
        r#"
            int main(void) { return 0; }
        "#,
    );
    let out_s = dir.path().join("out.s");

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.args(["build", "-S", "-o"]).arg(&out_s).arg(&main_c);
    cmd.assert().success();

    let meta = fs::metadata(&out_s).expect("assembly exists");
    assert!(meta.len() > 0, "assembly should be non-empty");
}

#[test]
fn compile_object_with_c_and_o() {
    let dir = tempdir().unwrap();
    let main_c = write_file(
        &dir,
        "main.c",
        r#"
            int main(void) { return 0; }
        "#,
    );
    let out_o = dir.path().join("out.o");

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.args(["build", "-c", "-o"]).arg(&out_o).arg(&main_c);
    cmd.assert().success();

    let meta = fs::metadata(&out_o).expect("object exists");
    assert!(meta.len() > 0, ".o should be non-empty");
}

#[test]
fn link_executable_with_o_and_run() {
    let dir = tempdir().unwrap();
    let main_c = write_file(
        &dir,
        "main.c",
        r#"
            int printf(const char*, ...);
            int main(void) { printf("ok\n"); return 0; }
        "#,
    );
    let prog = dir.path().join("prog");

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.args(["build", "-o"]).arg(&prog).arg(&main_c);
    cmd.assert().success();

    // Run the produced executable and capture stdout
    let out = Command::new(&prog).output().expect("run prog");
    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("ok\n"), "stdout was: {}", stdout);
}

#[test]
fn multi_input_linking_via_extra_args() {
    // Build a secondary object with clang and pass it to wyrmcc link via extra args ("-- ...")
    // Layout: lib.c -> lib.o via clang; main.c calls extern add; wyrmcc builds main.o and links with lib.o
    let dir = tempdir().unwrap();
    let lib_c = write_file(
        &dir,
        "lib.c",
        r#"
            int add(int a, int b) { return a + b; }
        "#,
    );
    let lib_o = dir.path().join("lib.o");

    // Detect clang executable (prefer clang-18, fallback to clang)
    let clang_cmd = if Command::new("clang-18")
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .ok()
        .map(|s| s.success())
        .unwrap_or(false)
    {
        "clang-18".to_string()
    } else {
        "clang".to_string()
    };

    // Compile lib.c with system clang (driver relies on clang for linking anyway)
    let status = Command::new(&clang_cmd)
        .args(["-c"]) // compile only
        .arg(&lib_c)
        .arg("-o")
        .arg(&lib_o)
        .status()
        .expect("spawn clang");
    assert!(status.success(), "clang -c lib.c failed");

    let main_c = write_file(
        &dir,
        "main.c",
        r#"
            int printf(const char*, ...);
            extern int add(int,int);
            int main(void){ printf("%d\n", add(3,4)); return 0; }
        "#,
    );
    let prog = dir.path().join("prog");

    // wyrmcc build main.c -o prog -- lib.o
    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.arg("build").arg(&main_c).args(["-o"]).arg(&prog).arg("--").arg(&lib_o);
    cmd.assert().success();

    let out = Command::new(&prog).output().expect("run prog");
    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("7\n"), "stdout was: {}", stdout);
}