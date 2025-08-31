#[cfg(unix)]
use assert_cmd::prelude::*;
#[cfg(unix)]
use predicates::str::contains;
#[cfg(unix)]
use std::fs;
#[cfg(unix)]
use std::io::Write;
#[cfg(unix)]
use std::process::Command;
#[cfg(unix)]
use tempfile::tempdir;

// Use tool names so the OS PATH resolves to the correct binaries.
#[cfg(unix)]
fn llvm_tools() -> (&'static str, &'static str) {
    ("clang-18", "llc-18")
}

#[cfg(unix)]
#[test]
fn run_descendant_infinite_loop_times_out() {
    let (clang, llc) = llvm_tools();

    let dir = tempdir().unwrap();
    let c_path = dir.path().join("fork_loop.c");
    let mut f = fs::File::create(&c_path).unwrap();
    writeln!(
        f,
        "{}",
        r#"#include <unistd.h>
#include <sys/types.h>
int main(void) {
    pid_t pid = fork();
    if (pid == 0) {
        for(;;){}
    } else if (pid > 0) {
        for(;;){}
    } else {
        return 1;
    }
    return 0;
}
"#
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .env("WYRMC_TIMEOUT_SECS", "1")
        .args(["run", c_path.to_string_lossy().as_ref()]);

    // Expect a timeout-induced failure and error mention
    cmd.assert().failure().stderr(contains("timed out"));
}

#[cfg(not(unix))]
#[test]
fn run_descendant_infinite_loop_times_out_skip() {
    // Not applicable on non-Unix platforms; group-kill semantics are Unix-specific.
    assert!(true);
}
