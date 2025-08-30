use pp::Preprocessor;

#[test]
fn basic_stringify() {
    let mut pp = Preprocessor::new();
    let src = "#define STR(x) #x\nSTR(hello   world)\n";
    let out = pp.preprocess_to_string(src);
    assert_eq!(out.trim_end(), "\"hello world\"");
}

#[test]
fn whitespace_collapse() {
    let mut pp = Preprocessor::new();
    let src = "#define STR(x) #x\nSTR(a    +   b)\n";
    let out = pp.preprocess_to_string(src);
    assert_eq!(out.trim_end(), "\"a + b\"");
}

#[test]
fn quotes_and_backslashes() {
    // Argument tokens: \"  \\  \"
    // Our toy PP escapes quotes as \" and doubles backslashes in the middle segment.
    let mut pp = Preprocessor::new();
    let src = "#define STR(x) #x\nSTR(\\\" \\\\ \\\")\n";
    let out = pp.preprocess_to_string(src);

    let got = out.trim_end().to_string();
    assert!(got.starts_with('"') && got.ends_with('"'), "got={:?}", got);

    let inner = &got[1..got.len()-1]; // strip outer quotes
    assert!(inner.starts_with(r#"\""#) && inner.ends_with(r#"\""#), "inner={:?}", inner);

    let mid = &inner[2..inner.len()-2]; // strip leading and trailing \"
    assert_eq!(mid, r#" \\\\ "#, "mid={:?}", mid); // exactly four backslashes with spaces
}

#[test]
fn no_expansion_inside_stringify() {
    // Ensure parameters referenced by # are not expanded before stringification
    let mut pp = Preprocessor::new();
    let src = "#define B 5\n#define STR(x) #x\nSTR(B + 1)\n";
    let out = pp.preprocess_to_string(src);
    assert_eq!(out.trim_end(), "\"B + 1\"");
}

#[test]
fn parentheses_wrapping_trimmed() {
    // Our toy PP trims a single outer pair of parentheses around the entire arg before expansion
    let mut pp = Preprocessor::new();
    let src = "#define STR(x) #x\nSTR((x + y))\n";
    let out = pp.preprocess_to_string(src);
    // With our current implementation, the outer parens are removed for stringify input
    assert_eq!(out.trim_end(), "\"x + y\"");
}