use lex::{Lexer, LiteralKind, TokenKind as K};

#[test]
fn lex_string_basic_and_escape() {
    let src = "\"hello\\n\";";
    let mut lx = Lexer::new(src);
    let tok = lx.next_token().expect("token");
    match tok.kind {
        K::Literal(LiteralKind::String { ref repr }) => {
            assert!(repr.starts_with('"') && repr.ends_with('"'));
            assert!(repr.contains("hello"));
            assert!(repr.contains("\\n") || repr.contains("\\x0a") || repr.contains("\\012"));
        }
        other => panic!("expected string literal, got: {:?}", other),
    }
}

#[test]
fn lex_char_basic() {
    let src = "'A';";
    let mut lx = Lexer::new(src);
    let tok = lx.next_token().expect("token");
    match tok.kind {
        K::Literal(LiteralKind::Char { ref repr }) => {
            assert_eq!(repr, "'A'");
        }
        other => panic!("expected char literal, got: {:?}", other),
    }
}

#[test]
fn lex_char_escape_newline() {
    let src = "'\\n';";
    let mut lx = Lexer::new(src);
    let tok = lx.next_token().expect("token");
    assert!(matches!(tok.kind, K::Literal(LiteralKind::Char { .. })));
}

#[test]
fn lex_char_hex_and_octal() {
    for s in ["'\\x41';", "'\\101';"] {
        let mut lx = Lexer::new(s);
        let tok = lx.next_token().expect("token");
        assert!(
            matches!(tok.kind, K::Literal(LiteralKind::Char { .. })),
            "not a char literal for {}",
            s
        );
    }
}
