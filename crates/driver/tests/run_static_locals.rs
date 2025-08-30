use assert_cmd::prelude::*;
use std::fs;
use std::io::Write;
use std::process::Command;
use tempfile::tempdir;

// Use tool names so the OS PATH resolves to the correct binaries.
fn llvm_tools() -> (&'static str, &'static str) {
    ("clang-18", "llc-18")
}

#[test]
fn run_static_local_persists_across_calls() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let c_path = dir.path().join("static_local.c");
    let mut f = fs::File::create(&c_path).unwrap();
    // int f(void){ static int s; s = s + 1; return s; }
    // main calls f() twice; second return should be 2 if static persists.
    writeln!(
        f,
        "int f(void){{ static int s; s = s + 1; return s; }} int main(void){{ int a=f(); int b=f(); return b; }}"
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", c_path.to_string_lossy().as_ref()]);

    // Expect the process to exit with code 2 (second call returns 2)
    cmd.assert().code(2);
}
