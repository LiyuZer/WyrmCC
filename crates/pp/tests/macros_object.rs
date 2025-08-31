use pp::Preprocessor;

fn squash(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

#[test]
fn define_object_basic() {
    let mut pp = Preprocessor::new();
    let src = "#define FOO 42\nint x = FOO;\n";
    let out = pp.preprocess_to_string(src);
    assert!(squash(&out).contains("intx=42;"), "output was:\n{}", out);
}

#[test]
fn multiple_substitutions_same_line() {
    let mut pp = Preprocessor::new();
    let src = "#define FOO 42\nint y = FOO+FOO;\n";
    let out = pp.preprocess_to_string(src);
    assert!(squash(&out).contains("inty=42+42;"), "output was:\n{}", out);
}

#[test]
fn undef_restores_identifier() {
    let mut pp = Preprocessor::new();
    let src = "#define FOO 1\n#undef FOO\nint z = FOO;\n";
    let out = pp.preprocess_to_string(src);
    // After undef, FOO should remain as an identifier (no expansion)
    assert!(squash(&out).contains("intz=FOO;"), "output was:\n{}", out);
}

#[test]
fn define_with_line_continuation() {
    let mut pp = Preprocessor::new();
    let src = "#define A 1 \\\n+ 2\nint r = A;\n";
    let out = pp.preprocess_to_string(src);
    // Accept either spaced or unspaced form (1+2)
    let squashed = squash(&out);
    assert!(squashed.contains("intr=1+2;"), "output was:\n{}", out);
}

#[test]
fn nested_non_recursive_guard() {
    let mut pp = Preprocessor::new();
    let src = "#define A B\n#define B 7\nint r = A;\n";
    let out = pp.preprocess_to_string(src);
    assert!(squash(&out).contains("intr=7;"), "output was:\n{}", out);
}
