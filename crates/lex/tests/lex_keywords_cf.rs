use lex::{Keyword as Kw, Lexer, LiteralKind, Punctuator as P, TokenKind as K};

fn toks(src: &str) -> Vec<lex::Token> {
    let mut lx = Lexer::new(src);
    std::iter::from_fn(|| lx.next_token()).collect()
}

#[test]
fn keyword_if_else_tokens() {
    let ts = toks("if (x) { } else { }");
    use K::*;
    assert!(matches!(ts[0].kind, Keyword(Kw::If)));
    assert!(matches!(ts[1].kind, Punct(P::LParen)));
    assert!(matches!(ts[2].kind, Identifier(ref s) if s == "x"));
    assert!(matches!(ts[3].kind, Punct(P::RParen)));
    assert!(matches!(ts[4].kind, Punct(P::LBrace)));
    assert!(matches!(ts[5].kind, Punct(P::RBrace)));
    assert!(matches!(ts[6].kind, Keyword(Kw::Else)));
    assert!(matches!(ts[7].kind, Punct(P::LBrace)));
    assert!(matches!(ts[8].kind, Punct(P::RBrace)));
}

#[test]
fn while_break_continue_tokens() {
    let ts = toks("while (1) break; continue;");
    use K::*;
    assert!(matches!(ts[0].kind, Keyword(Kw::While)));
    assert!(matches!(ts[1].kind, Punct(P::LParen)));
    assert!(matches!(ts[2].kind, Literal(LiteralKind::Int { .. })));
    assert!(matches!(ts[3].kind, Punct(P::RParen)));
    assert!(matches!(ts[4].kind, Keyword(Kw::Break)));
    assert!(matches!(ts[5].kind, Punct(P::Semicolon)));
    assert!(matches!(ts[6].kind, Keyword(Kw::Continue)));
    assert!(matches!(ts[7].kind, Punct(P::Semicolon)));
}

#[test]
fn keywords_not_identifiers_when_longer() {
    // Ensure similar-looking identifiers are not treated as keywords
    let ts = toks("ifx elsey whilez breakk continueu");
    use K::*;
    assert!(matches!(ts[0].kind, Identifier(ref s) if s == "ifx"));
    assert!(matches!(ts[1].kind, Identifier(ref s) if s == "elsey"));
    assert!(matches!(ts[2].kind, Identifier(ref s) if s == "whilez"));
    assert!(matches!(ts[3].kind, Identifier(ref s) if s == "breakk"));
    assert!(matches!(ts[4].kind, Identifier(ref s) if s == "continueu"));
}
