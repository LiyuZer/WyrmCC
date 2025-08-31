use std::fs;
use std::path::{Path, PathBuf};

use pp::Preprocessor;

fn write(p: &Path, name: &str, content: &str) -> PathBuf {
    let f = p.join(name);
    fs::create_dir_all(f.parent().unwrap()).unwrap();
    fs::write(&f, content).unwrap();
    f
}

fn tempdir() -> PathBuf {
    let base = std::env::temp_dir();
    let unique = format!(
        "wyrmcc_pp_test_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    );
    let dir = base.join(unique);
    fs::create_dir_all(&dir).unwrap();
    dir
}

#[test]
fn include_quoted_searches_current_then_I() {
    // Layout:
    // tmp/
    //   foo.h           -> defines X
    //   main.c          -> includes "foo.h" and uses X
    let root = tempdir();

    write(&root, "foo.h", "#define X 7\n");
    let main_c = write(&root, "main.c", "#include \"foo.h\"\nint x = X;\n");

    // Quoted include must search current dir first; no -I needed
    let mut pp = Preprocessor::new();
    let out = pp
        .preprocess_file_with_includes(&main_c, &[])
        .expect("preprocess ok");
    assert!(out.replace(' ', "").contains("intx=7;"), "{}", out);
}

#[test]
fn include_angled_searches_I_only() {
    // Layout:
    // tmp/
    //   src/main.c      -> includes <bar.h> and uses Y
    //   inc/bar.h       -> defines Y
    let root = tempdir();
    let inc = root.join("inc");
    let src = root.join("src");

    write(&inc, "bar.h", "#define Y 42\n");
    let main_c = write(&src, "main.c", "#include <bar.h>\nint y = Y;\n");

    let mut pp = Preprocessor::new();
    // Angle-bracket include should search only -I paths, not current dir
    let out = pp
        .preprocess_file_with_includes(&main_c, &[inc.clone()])
        .expect("preprocess ok");
    assert!(out.replace(' ', "").contains("inty=42;"), "{}", out);
}

#[test]
fn include_cycle_is_detected_and_reported() {
    // Layout with a cycle: a.h -> b.h -> a.h
    let root = tempdir();

    write(&root, "a.h", "#include \"b.h\"\n#define A 1\n");
    write(&root, "b.h", "#include \"a.h\"\n#define B 2\n");
    let main_c = write(&root, "main.c", "#include \"a.h\"\nint z = A + B;\n");

    let mut pp = Preprocessor::new();
    let res = pp.preprocess_file_with_includes(&main_c, &[]);
    assert!(
        res.is_err(),
        "expected include-cycle error but got: {:?}",
        res
    );
    let err = res.err().unwrap();
    assert!(
        err.to_string().to_lowercase().contains("cycle"),
        "unexpected error: {}",
        err
    );
}
