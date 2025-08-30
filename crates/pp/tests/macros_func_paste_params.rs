use pp::Preprocessor;

#[test]
fn paste_param_simple() {
    let mut pp = Preprocessor::new();
    let src = "#define CAT(a,b) a ## b\nCAT(foo, bar)\n";
    let out = pp.preprocess_to_string(src);
    assert_eq!(out.trim_end(), "foobar");
}

#[test]
fn paste_param_rhs_multi_tokens() {
    // When the RHS parameter expands to multiple tokens, only the first token pastes;
    // the remaining tokens should be emitted after the combined token.
    let mut pp = Preprocessor::new();
    let src = "#define A 1 + 2\n#define CATX(x) X ## x\nCATX(A)\n";
    let out = pp.preprocess_to_string(src);
    assert_eq!(out.trim_end(), "X1 + 2");
}

#[test]
fn paste_param_lhs_multi_tokens() {
    // For a ## with a parameter on the LHS that expands to multiple tokens,
    // the last emitted non-whitespace LHS token pastes with the RHS token.
    let mut pp = Preprocessor::new();
    let src = "#define A 1 + 2\n#define CAT2(a) a ## Z\nCAT2(A)\n";
    let out = pp.preprocess_to_string(src);
    assert_eq!(out.trim_end(), "1 + 2Z");
}

#[test]
fn paste_chain() {
    // Chained pastes: a ## b ## c -> paste a with b, then paste the result with c.
    // Our toy preprocessor permits arbitrary combined tokens like "4+9".
    let mut pp = Preprocessor::new();
    let src = "#define A 4\n#define CAT3(a,b,c) a ## b ## c\nCAT3(A, +, 9)\n";
    let out = pp.preprocess_to_string(src);
    assert_eq!(out.trim_end(), "4+9");
}

#[test]
fn paste_with_whitespace() {
    // Whitespace around ## should not affect the concatenation result.
    let mut pp = Preprocessor::new();
    let src = "#define CAT(a,b) a  ##   b\nCAT(FOO, 7)\n";
    let out = pp.preprocess_to_string(src);
    assert_eq!(out.trim_end(), "FOO7");
}
