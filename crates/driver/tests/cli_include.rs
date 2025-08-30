use assert_cmd::prelude::*;
use predicates::prelude::*;
use std::fs::{self, File};
use std::io::Write;
use std::process::Command;
use tempfile::tempdir;

#[test]
fn preprocess_include_quoted_current_dir() {
    // Layout:
    // tmp/
    //   foo.h     -> defines X
    //   main.c    -> includes "foo.h" and uses X
    let dir = tempdir().unwrap();
    let root = dir.path();

    fs::write(root.join("foo.h"), "#define X 7\n").unwrap();

    let main_c = root.join("main.c");
    let mut f = File::create(&main_c).unwrap();
    writeln!(f, "#include \"foo.h\"").unwrap();
    writeln!(f, "int x = X;").unwrap();

    // Quoted include must search current dir first; no -I needed
    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.args(["preprocess", main_c.to_string_lossy().as_ref()]);

    cmd.assert()
        .success()
        .stdout(predicate::str::contains("int x = 7"));
}

#[test]
fn preprocess_include_angled_search_I() {
    // Layout:
    // tmp/
    //   inc/bar.h  -> defines Y
    //   src/main.c -> includes <bar.h> and uses Y
    let dir = tempdir().unwrap();
    let inc = dir.path().join("inc");
    let src = dir.path().join("src");
    fs::create_dir_all(&inc).unwrap();
    fs::create_dir_all(&src).unwrap();

    fs::write(inc.join("bar.h"), "#define Y 42\n").unwrap();

    let main_c = src.join("main.c");
    let mut f = File::create(&main_c).unwrap();
    writeln!(f, "#include <bar.h>").unwrap();
    writeln!(f, "int y = Y;").unwrap();

    // Angle-bracket include should search only -I paths, not current dir
    let mut cmd = Command::cargo_bin("wyrmcc").unwrap();
    cmd.arg("preprocess")
        .arg("-I")
        .arg(inc.to_string_lossy().as_ref())
        .arg(main_c.to_string_lossy().as_ref());

    cmd.assert()
        .success()
        .stdout(predicate::str::contains("int y = 42"));
}
