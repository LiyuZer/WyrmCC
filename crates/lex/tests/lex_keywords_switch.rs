use lex::{Lexer, TokenKind as K, Keyword as Kw, Punctuator as P, LiteralKind};

fn toks(src: &str) -> Vec<lex::Token> {
    let mut lx = Lexer::new(src);
    std::iter::from_fn(|| lx.next_token()).collect()
}

#[test]
fn switch_case_default_tokens() {
    let ts = toks("switch (x) { case 1: default: }");
    use K::*;

    assert!(matches!(ts[0].kind, Keyword(Kw::Switch)));
    assert!(matches!(ts[1].kind, Punct(P::LParen)));
    assert!(matches!(ts[2].kind, Identifier(ref s) if s == "x"));
    assert!(matches!(ts[3].kind, Punct(P::RParen)));
    assert!(matches!(ts[4].kind, Punct(P::LBrace)));

    assert!(matches!(ts[5].kind, Keyword(Kw::Case)));
    assert!(matches!(ts[6].kind, Literal(LiteralKind::Int { .. })));
    assert!(matches!(ts[7].kind, Punct(P::Colon)));

    assert!(matches!(ts[8].kind, Keyword(Kw::Default)));
    assert!(matches!(ts[9].kind, Punct(P::Colon)));
    assert!(matches!(ts[10].kind, Punct(P::RBrace)));
}

#[test]
fn switch_multiple_cases_and_stmt_tokens() {
    let ts = toks("switch (x) { case 1: case 2: y = 3; }");
    use K::*;

    // Basic header
    assert!(matches!(ts[0].kind, Keyword(Kw::Switch)));
    assert!(matches!(ts[1].kind, Punct(P::LParen)));
    assert!(matches!(ts[2].kind, Identifier(ref s) if s == "x"));
    assert!(matches!(ts[3].kind, Punct(P::RParen)));
    assert!(matches!(ts[4].kind, Punct(P::LBrace)));

    // Expect two case labels: `case 1:` and `case 2:`
    let mut case_ix = vec![];
    for (i, t) in ts.iter().enumerate() {
        if matches!(t.kind, Keyword(Kw::Case)) { case_ix.push(i); }
    }
    assert_eq!(case_ix.len(), 2);

    // For each case, next tokens should be an int literal then colon
    for &i in &case_ix {
        assert!(matches!(ts[i+1].kind, Literal(LiteralKind::Int { .. })));
        assert!(matches!(ts[i+2].kind, Punct(P::Colon)));
    }

    // Statement: y = 3; and closing brace
    // Find `y`
    let mut yi = None;
    for (i, t) in ts.iter().enumerate() {
        if matches!(t.kind, Identifier(ref s) if s == "y") { yi = Some(i); break; }
    }
    let yi = yi.expect("identifier y present");
    assert!(matches!(ts[yi+1].kind, Punct(P::Assign)));
    assert!(matches!(ts[yi+2].kind, Literal(LiteralKind::Int { .. })));
    assert!(matches!(ts[yi+3].kind, Punct(P::Semicolon)));

    assert!(matches!(ts.last().unwrap().kind, Punct(P::RBrace)));
}
