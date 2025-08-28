use assert_cmd::prelude::*;
use predicates::prelude::*;
use std::fs::File;
use std::io::Write;
use std::process::Command;
use tempfile::tempdir;

#[test]
fn ast_shows_function_main() {
    let dir = tempdir().unwrap();
    let file_path = dir.path().join("test.c");
    let mut f = File::create(&file_path).unwrap();
    writeln!(f, "int main(void) {{ return 0; }}").unwrap();

    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.args(["ast", file_path.to_string_lossy().as_ref()]);
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("functions"))
        .stdout(predicate::str::contains("name: \"main\""));
}
