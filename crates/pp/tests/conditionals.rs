use pp::Preprocessor;

fn squash(s: &str) -> String { s.chars().filter(|c| !c.is_whitespace()).collect() }

#[test]
fn ifdef_basic_defined() {
    let mut pp = Preprocessor::new();
    let src = "#define FOO 1\n#ifdef FOO\nint x=1;\n#else\nint x=0;\n#endif\n";
    let out = pp.preprocess_to_string(src);
    let sq = squash(&out);
    assert!(sq.contains("intx=1;"), "expected int x=1 present, got:\n{}", out);
    assert!(!sq.contains("intx=0;"), "did not expect int x=0, got:\n{}", out);
}

#[test]
fn ifdef_basic_undefined() {
    let mut pp = Preprocessor::new();
    let src = "#ifdef FOO\nint x=1;\n#else\nint x=0;\n#endif\n";
    let out = pp.preprocess_to_string(src);
    let sq = squash(&out);
    assert!(sq.contains("intx=0;"), "expected int x=0 present, got:\n{}", out);
    assert!(!sq.contains("intx=1;"), "did not expect int x=1, got:\n{}", out);
}

#[test]
fn if_defined_paren_and_noparen() {
    let mut pp = Preprocessor::new();
    let src = "#define BAR 1\n#if defined(BAR)\nint a=1;\n#endif\n#if defined BAZ\nint b=1;\n#else\nint b=0;\n#endif\n";
    let out = pp.preprocess_to_string(src);
    let sq = squash(&out);
    assert!(sq.contains("inta=1;"), "expected int a=1 present, got:\n{}", out);
    assert!(sq.contains("intb=0;"), "expected int b=0 present, got:\n{}", out);
    assert!(!sq.contains("intb=1;"), "did not expect int b=1, got:\n{}", out);
}

#[test]
fn elif_chain() {
    let mut pp = Preprocessor::new();
    let src = "#define F 0\n#if F==1\nint r=1;\n#elif F==0\nint r=2;\n#else\nint r=3;\n#endif\n";
    let out = pp.preprocess_to_string(src);
    let sq = squash(&out);
    assert!(sq.contains("intr=2;"), "expected int r=2 present, got:\n{}", out);
    assert!(!sq.contains("intr=1;"), "did not expect int r=1, got:\n{}", out);
    assert!(!sq.contains("intr=3;"), "did not expect int r=3, got:\n{}", out);
}

#[test]
fn logical_ops_and_parens() {
    let mut pp = Preprocessor::new();
    let src = "#define X 1\n#define Y 0\n#if (defined(X) && X==1) || (defined(Y) && Y==1)\nint v=42;\n#else\nint v=7;\n#endif\n";
    let out = pp.preprocess_to_string(src);
    let sq = squash(&out);
    assert!(sq.contains("intv=42;"), "expected int v=42 present, got:\n{}", out);
    assert!(!sq.contains("intv=7;"), "did not expect int v=7, got:\n{}", out);
}

#[test]
fn nested_conditionals() {
    let mut pp = Preprocessor::new();
    let src = "#define OUT 1\n#if OUT\n  #ifdef IN\n  int z=1;\n  #else\n  int z=2;\n  #endif\n#else\n  int z=3;\n#endif\n";
    let out = pp.preprocess_to_string(src);
    let sq = squash(&out);
    assert!(sq.contains("intz=2;"), "expected int z=2 present, got:\n{}", out);
    assert!(!sq.contains("intz=1;"), "did not expect int z=1, got:\n{}", out);
    assert!(!sq.contains("intz=3;"), "did not expect int z=3, got:\n{}", out);
}
