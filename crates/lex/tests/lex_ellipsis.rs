use lex::{Lexer, TokenKind as K, Punctuator as P};

#[test]
fn lex_ellipsis_token() {
    let mut lx = Lexer::new("f(...)");
    let mut kinds = Vec::new();
    while let Some(t) = lx.next_token() { kinds.push(t.kind.clone()); }

    assert!(matches!(kinds.get(0), Some(K::Identifier(s)) if s == "f"), "expected ident 'f', got {:?}", kinds.get(0));
    assert!(matches!(kinds.get(1), Some(K::Punct(p)) if *p == P::LParen), "expected '(', got {:?}", kinds.get(1));
    // New token: Ellipsis
    assert!(matches!(kinds.get(2), Some(K::Punct(p)) if *p == P::Ellipsis), "expected '...', got {:?}", kinds.get(2));
    assert!(matches!(kinds.get(3), Some(K::Punct(p)) if *p == P::RParen), "expected ')', got {:?}", kinds.get(3));
}

#[test]
fn lex_dot_still_works() {
    let mut lx = Lexer::new("s.a");
    let mut kinds = Vec::new();
    while let Some(t) = lx.next_token() { kinds.push(t.kind.clone()); }

    assert!(matches!(kinds.get(0), Some(K::Identifier(s)) if s == "s"), "expected ident 's', got {:?}", kinds.get(0));
    assert!(matches!(kinds.get(1), Some(K::Punct(p)) if *p == P::Dot), "expected '.', got {:?}", kinds.get(1));
    assert!(matches!(kinds.get(2), Some(K::Identifier(s)) if s == "a"), "expected ident 'a', got {:?}", kinds.get(2));
}
