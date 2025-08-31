use pp::Preprocessor;

#[test]
fn stringify_basic() {
    let src = "\
#define STR(x) #x
int x = 0;
const char* s = STR(hello   world  +  1);
";
    let mut pp = Preprocessor::new();
    let out = pp.preprocess_to_string(src);
    assert!(out.contains("\"hello world + 1\""), "got:\n{}", out);
}

#[test]
fn stringify_escapes() {
    let src = "\
#define STR(x) #x
const char* s = STR(a\\b\\\"c);
";
    let mut pp = Preprocessor::new();
    let out = pp.preprocess_to_string(src);
    // Expect backslashes and quotes escaped inside the produced string literal
    assert!(out.contains("\"a\\\\b\\\"c\""), "got:\n{}", out);
}

#[test]
fn token_paste_ident() {
    let src = "\
#define CAT(a,b) a ## b
int foobar = 1;
int x = CAT(foo,bar);
";
    let mut pp = Preprocessor::new();
    let out = pp.preprocess_to_string(src);
    assert!(out.contains("int x = foobar;"), "got:\n{}", out);
}

#[test]
fn token_paste_number() {
    let src = "\
#define CAT2(a,b) a ## b
int x = CAT2(12,34);
";
    let mut pp = Preprocessor::new();
    let out = pp.preprocess_to_string(src);
    assert!(out.contains("int x = 1234;"), "got:\n{}", out);
}

#[test]
fn token_paste_mkid() {
    let src = "\
#define MKID(n) var ## n
int var2 = 7;
int y = MKID(2);
";
    let mut pp = Preprocessor::new();
    let out = pp.preprocess_to_string(src);
    assert!(out.contains("int y = var2;"), "got:\n{}", out);
}
