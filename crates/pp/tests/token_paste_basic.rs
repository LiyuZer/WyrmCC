use pp::Preprocessor;

fn run_pp(src: &str) -> String {
    let mut pp = Preprocessor::new();
    pp.preprocess_to_string(src)
}

#[test]
fn token_paste_basic() {
    // Object and function-like token pasting basics
    // - Object macros: A##B -> foobar
    // - Function-like: CAT(1,2) -> 12; G2(>,>) -> >>; G2(>,=) -> >=
    let src = r#"
#define A foo
#define B bar
#define C A##B
#define CAT(a,b) a ## b
#define G2(x,y) x ## y
C
CAT(1,2)
G2(>,>)
G2(>,=)
"#;

    let out = run_pp(src);
    // Normalize lines
    let lines: Vec<String> = out
        .lines()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty() && !s.starts_with('#'))
        .collect();

    // Expect expansions present; order corresponds to the four invocation lines
    assert!(
        lines.iter().any(|l| l.contains("foobar")),
        "expected foobar in output:\n{}",
        out
    );
    assert!(
        lines.iter().any(|l| l.contains("12")),
        "expected 12 in output:\n{}",
        out
    );
    assert!(
        lines.iter().any(|l| l.contains(">>")),
        "expected >> in output:\n{}",
        out
    );
    assert!(
        lines.iter().any(|l| l.contains(">=")),
        "expected >= in output:\n{}",
        out
    );
}
