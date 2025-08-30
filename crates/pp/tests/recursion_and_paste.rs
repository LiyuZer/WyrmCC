use pp::Preprocessor;

fn squash(s: &str) -> String { s.chars().filter(|c| !c.is_whitespace()).collect() }

#[test]
fn mutual_func_recursion_capped() {
    // Two mutually-recursive function-like macros should not blow up.
    // With the active-set guard and depth cap, expansion should stabilize
    // to a bounded form that still contains one of the macro calls.
    let mut pp = Preprocessor::new();
    let src = "#define A(x) B(x)\n#define B(x) A(x)\nint r = A(7);\n";
    let out = pp.preprocess_to_string(src);
    let squashed = squash(&out);
    assert!(
        squashed.contains("intr=A(7);") || squashed.contains("intr=B(7);"),
        "output was:\n{}",
        out
    );
}

#[test]
fn token_paste_basic_and_ws() {
    // Ensure the tokenizer recognizes '##' and substitute_with_ops pastes correctly,
    // ignoring surrounding whitespace and combining nearest non-whitespace tokens.
    let mut pp = Preprocessor::new();
    let src = "#define JOIN(a,b) a ## b\n\
               int x = JOIN(hello, world);\n\
               int y = JOIN( foo , bar );\n\
               int z = JOIN(1, 2);\n";
    let out = pp.preprocess_to_string(src);
    let squashed = squash(&out);
    assert!(squashed.contains("intx=helloworld;"), "output was:\n{}", out);
    assert!(squashed.contains("inty=foobar;"), "output was:\n{}", out);
    assert!(squashed.contains("intz=12;"), "output was:\n{}", out);
}
