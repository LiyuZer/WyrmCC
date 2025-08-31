use lex::{Keyword, Lexer, LiteralKind, Punctuator, TokenKind};

#[test]
fn basic_c_tokens_sequence() {
    let src = r#"
        int main(void) {
            int y = 3 + 4;
            if (y >= 7) return y; else return 0;
        }
    "#;
    let mut lx = Lexer::new(src);
    let toks: Vec<_> = std::iter::from_fn(|| lx.next_token()).collect();

    use Punctuator as P;
    use TokenKind as K;

    // Spot-check sequence
    assert!(matches!(toks[0].kind, K::Keyword(Keyword::Int)));
    assert!(matches!(toks[1].kind, K::Identifier(ref s) if s == "main"));
    assert!(matches!(toks[2].kind, K::Punct(P::LParen)));
    assert!(matches!(toks[3].kind, K::Keyword(Keyword::Void)));
    assert!(matches!(toks[4].kind, K::Punct(P::RParen)));
    assert!(matches!(toks[5].kind, K::Punct(P::LBrace)));

    // y = 3 + 4 ;
    let mut i = 0;
    while i < toks.len() && !matches!(toks[i].kind, K::Identifier(ref s) if s == "y") {
        i += 1;
    }
    assert!(i + 5 < toks.len());
    assert!(matches!(toks[i].kind,     K::Identifier(ref s) if s == "y"));
    assert!(matches!(toks[i + 1].kind, K::Punct(P::Assign)));
    assert!(matches!(
        toks[i + 2].kind,
        K::Literal(LiteralKind::Int { .. })
    ));
    assert!(matches!(toks[i + 3].kind, K::Punct(P::Plus)));
    assert!(matches!(
        toks[i + 4].kind,
        K::Literal(LiteralKind::Int { .. })
    ));

    // if (y >= 7)
    let mut j = 0;
    while j < toks.len() && !matches!(toks[j].kind, K::Keyword(Keyword::If)) {
        j += 1;
    }
    assert!(j + 5 < toks.len());
    assert!(matches!(toks[j].kind, K::Keyword(Keyword::If)));
    assert!(matches!(toks[j + 1].kind, K::Punct(P::LParen)));
    assert!(matches!(toks[j+2].kind,   K::Identifier(ref s) if s == "y"));
    assert!(matches!(toks[j + 3].kind, K::Punct(P::Ge)));
    assert!(matches!(
        toks[j + 4].kind,
        K::Literal(LiteralKind::Int { .. })
    ));
    assert!(matches!(toks[j + 5].kind, K::Punct(P::RParen)));
}
