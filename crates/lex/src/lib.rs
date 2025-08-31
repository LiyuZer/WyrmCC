pub mod keywords;
mod lexer;
pub mod token;

pub use lexer::Lexer;
pub use token::{IntBase, Keyword, LiteralKind, Punctuator, Span, Token, TokenKind};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex_ident_keyword_number() {
        let src = "int x = 42;";
        let mut lx = Lexer::new(src);
        let toks: Vec<_> = std::iter::from_fn(|| lx.next_token()).collect();
        use TokenKind as K;
        assert!(matches!(toks[0].kind, K::Keyword(Keyword::Int)));
        assert!(matches!(toks[1].kind, K::Identifier(ref s) if s == "x"));
        assert!(matches!(toks[2].kind, K::Punct(Punctuator::Assign)));
        assert!(matches!(toks[3].kind, K::Literal(LiteralKind::Int { .. })));
        assert!(matches!(toks[4].kind, K::Punct(Punctuator::Semicolon)));
    }
}
