use assert_cmd::prelude::*;
use std::fs::File;
use std::io::Write;
use std::process::Command;
use tempfile::tempdir;

fn tools() -> (&'static str, &'static str) {
    ("clang-18", "llc-18")
}

#[test]
fn run_if_else_returns_2() {
    let (clang, llc) = tools();
    let dir = tempdir().unwrap();
    let p = dir.path().join("t.c");
    let mut f = File::create(&p).unwrap();
    writeln!(f, "int main(void) {{ if (0) return 1; else return 2; }}").unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", p.to_string_lossy().as_ref()]);
    cmd.assert().code(2);
}

#[test]
fn run_while_false_skips_body() {
    let (clang, llc) = tools();
    let dir = tempdir().unwrap();
    let p = dir.path().join("t.c");
    let mut f = File::create(&p).unwrap();
    writeln!(
        f,
        "int main(void) {{ while (0) {{ return 3; }} return 5; }}"
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", p.to_string_lossy().as_ref()]);
    cmd.assert().code(5);
}

#[test]
fn run_while_true_breaks_immediately() {
    let (clang, llc) = tools();
    let dir = tempdir().unwrap();
    let p = dir.path().join("t.c");
    let mut f = File::create(&p).unwrap();
    writeln!(f, "int main(void) {{ while (1) {{ break; }} return 7; }}").unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["run", p.to_string_lossy().as_ref()]);
    cmd.assert().code(7);
}

#[test]
fn ir_if_else_contains_labels() {
    let (clang, llc) = tools();
    let dir = tempdir().unwrap();
    let p = dir.path().join("t.c");
    let mut f = File::create(&p).unwrap();
    writeln!(f, "int main(void) {{ if (1) return 1; else return 2; }}").unwrap();

    let output = Command::cargo_bin("wyrmcc")
        .unwrap()
        .env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["emit-llvm", p.to_string_lossy().as_ref()])
        .output()
        .unwrap();
    assert!(output.status.success());
    let ir = String::from_utf8_lossy(&output.stdout);

    // Expect conditional branch and labeled blocks; backend label names may vary (e.g., L1, L2,...)
    assert!(
        ir.contains("br i1"),
        "IR should contain conditional branch: {}",
        ir
    );
    assert!(
        ir.contains("\nL") && ir.contains(":"),
        "IR should contain label blocks (L*): {}",
        ir
    );
}

#[test]
fn ir_while_break_continue_labels() {
    let (clang, llc) = tools();
    let dir = tempdir().unwrap();
    let p = dir.path().join("t.c");
    // continue; then break; (break may be unreachable after continue, still expect loop labels/branches)
    let mut f = File::create(&p).unwrap();
    writeln!(
        f,
        "int main(void) {{ while (1) {{ continue; break; }} return 0; }}"
    )
    .unwrap();

    let output = Command::cargo_bin("wyrmcc")
        .unwrap()
        .env("WYRMC_CLANG", clang)
        .env("WYRMC_LLC", llc)
        .args(["emit-llvm", p.to_string_lossy().as_ref()])
        .output()
        .unwrap();
    assert!(output.status.success());
    let ir = String::from_utf8_lossy(&output.stdout);

    // Expect multiple labels and a backedge/branch to some label (L*) for loop control
    assert!(
        ir.contains("\nL") && ir.contains(":"),
        "IR should contain loop labels (L*): {}",
        ir
    );
    assert!(
        ir.contains("br label %L"),
        "IR should branch to a label (loop backedge / continue): {}",
        ir
    );
}
