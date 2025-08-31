use lex::{Keyword as Kw, Lexer, LiteralKind, Punctuator as P, TokenKind as K};

fn toks(src: &str) -> Vec<lex::Token> {
    let mut lx = Lexer::new(src);
    std::iter::from_fn(|| lx.next_token()).collect()
}

#[test]
fn decl_type_keywords_tokenize() {
    let src = "auto register static extern const volatile struct union enum typedef";
    let ts = toks(src);
    use K::*;
    let mut i = 0;
    assert!(matches!(ts[i].kind, Keyword(Kw::Auto)));
    i += 1;
    assert!(matches!(ts[i].kind, Keyword(Kw::Register)));
    i += 1;
    assert!(matches!(ts[i].kind, Keyword(Kw::Static)));
    i += 1;
    assert!(matches!(ts[i].kind, Keyword(Kw::Extern)));
    i += 1;
    assert!(matches!(ts[i].kind, Keyword(Kw::Const)));
    i += 1;
    assert!(matches!(ts[i].kind, Keyword(Kw::Volatile)));
    i += 1;
    assert!(matches!(ts[i].kind, Keyword(Kw::Struct)));
    i += 1;
    assert!(matches!(ts[i].kind, Keyword(Kw::Union)));
    i += 1;
    assert!(matches!(ts[i].kind, Keyword(Kw::Enum)));
    i += 1;
    assert!(matches!(ts[i].kind, Keyword(Kw::Typedef)));
    i += 1;
    assert_eq!(i, ts.len());
}

#[test]
fn decl_type_keywords_not_identifiers_when_separate() {
    // Simple smoke around a declaration-like snippet
    let src = "extern int x; typedef int I; struct S { int a; };";
    let ts = toks(src);
    use K::*;
    let mut i = 0;
    assert!(matches!(ts[i].kind, Keyword(Kw::Extern)));
    i += 1;
    assert!(matches!(ts[i].kind, Keyword(Kw::Int)));
    i += 1;
    assert!(matches!(ts[i].kind, Identifier(ref s) if s == "x"));
    i += 1;
    assert!(matches!(ts[i].kind, Punct(P::Semicolon)));
    i += 1;

    assert!(matches!(ts[i].kind, Keyword(Kw::Typedef)));
    i += 1;
    assert!(matches!(ts[i].kind, Keyword(Kw::Int)));
    i += 1;
    assert!(matches!(ts[i].kind, Identifier(ref s) if s == "I"));
    i += 1;
    assert!(matches!(ts[i].kind, Punct(P::Semicolon)));
    i += 1;

    assert!(matches!(ts[i].kind, Keyword(Kw::Struct)));
    i += 1;
    assert!(matches!(ts[i].kind, Identifier(ref s) if s == "S"));
    i += 1;
    assert!(matches!(ts[i].kind, Punct(P::LBrace)));
    i += 1;
    assert!(matches!(ts[i].kind, Keyword(Kw::Int)));
    i += 1;
    assert!(matches!(ts[i].kind, Identifier(ref s) if s == "a"));
    i += 1;
    assert!(matches!(ts[i].kind, Punct(P::Semicolon)));
    i += 1;
    assert!(matches!(ts[i].kind, Punct(P::RBrace)));
    i += 1;
    assert!(matches!(ts[i].kind, Punct(P::Semicolon)));
    i += 1;

    assert!(i <= ts.len());
}

#[test]
fn near_miss_identifiers_not_keywords() {
    // Ensure similar-looking identifiers are not treated as keywords
    let src = "autox registery staticc externd constx volatiley structz unionw enumm typedefx";
    let ts = toks(src);
    use K::*;
    let mut i = 0;
    assert!(matches!(ts[i].kind, Identifier(ref s) if s == "autox"));
    i += 1;
    assert!(matches!(ts[i].kind, Identifier(ref s) if s == "registery"));
    i += 1;
    assert!(matches!(ts[i].kind, Identifier(ref s) if s == "staticc"));
    i += 1;
    assert!(matches!(ts[i].kind, Identifier(ref s) if s == "externd"));
    i += 1;
    assert!(matches!(ts[i].kind, Identifier(ref s) if s == "constx"));
    i += 1;
    assert!(matches!(ts[i].kind, Identifier(ref s) if s == "volatiley"));
    i += 1;
    assert!(matches!(ts[i].kind, Identifier(ref s) if s == "structz"));
    i += 1;
    assert!(matches!(ts[i].kind, Identifier(ref s) if s == "unionw"));
    i += 1;
    assert!(matches!(ts[i].kind, Identifier(ref s) if s == "enumm"));
    i += 1;
    assert!(matches!(ts[i].kind, Identifier(ref s) if s == "typedefx"));
    i += 1;
    assert_eq!(i, ts.len());
}
