use pp::Preprocessor;

fn squash(s: &str) -> String { s.chars().filter(|c| !c.is_whitespace()).collect() }

#[test]
fn define_func_basic() {
    let mut pp = Preprocessor::new();
    let src = "#define ADD(x,y) (x + y)\nint x = ADD(2, 40);\n";
    let out = pp.preprocess_to_string(src);
    assert!(squash(&out).contains("intx=(2+40);"), "output was:\n{}", out);
}

#[test]
fn nested_func_uses_object_and_func() {
    let mut pp = Preprocessor::new();
    let src = "#define X 3\n#define TWICE(a) ADD(a, a)\n#define ADD(x,y) (x + y)\nint r = TWICE(X);\n";
    let out = pp.preprocess_to_string(src);
    assert!(squash(&out).contains("intr=(3+3);"), "output was:\n{}", out);
}

#[test]
fn args_with_paren_and_commas() {
    let mut pp = Preprocessor::new();
    let src = "#define PAIR(a,b) (a * (b))\nint r = PAIR(1+2, (3+4));\n";
    let out = pp.preprocess_to_string(src);
    let squashed = squash(&out);
    assert!(squashed.contains("intr=(1+2*(3+4));"), "output was:\n{}", out);
}

#[test]
fn no_call_no_expand() {
    let mut pp = Preprocessor::new();
    let src = "#define F(x) (x+1)\nint r = F;\n";
    let out = pp.preprocess_to_string(src);
    assert!(squash(&out).contains("intr=F;"), "output was:\n{}", out);
}

#[test]
fn prevent_immediate_recursive_expansion() {
    let mut pp = Preprocessor::new();
    let src = "#define ID(x) ID(x)\nint r = ID(7);\n";
    let out = pp.preprocess_to_string(src);
    // We only require that it does not loop and leaves a stable form
    assert!(squash(&out).contains("intr=ID(7);"), "output was:\n{}", out);
}
