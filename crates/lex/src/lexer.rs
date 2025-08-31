use crate::keywords::to_keyword;
use crate::token::{IntBase, LiteralKind, Punctuator as P, Span, Token, TokenKind as K};

pub struct Lexer<'a> {
    src: &'a str,
    bytes: &'a [u8],
    len: usize,
    pos: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Self {
            src,
            bytes: src.as_bytes(),
            len: src.len(),
            pos: 0,
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }
    fn bump(&mut self) -> Option<u8> {
        let c = self.peek()?;
        self.pos += 1;
        Some(c)
    }
    fn starts_with(&self, s: &str) -> bool {
        self.bytes
            .get(self.pos..)
            .is_some_and(|rest| rest.starts_with(s.as_bytes()))
    }
    fn make_span(&self, start: usize) -> Span {
        Span {
            start,
            end: self.pos,
        }
    }

    fn is_ident_start(c: u8) -> bool {
        (c == b'_') || (c as char).is_ascii_alphabetic()
    }
    fn is_ident_continue(c: u8) -> bool {
        (c == b'_') || (c as char).is_ascii_alphanumeric()
    }

    fn skip_ws_and_comments(&mut self) {
        loop {
            // whitespace
            while matches!(self.peek(), Some(b' ' | b'\t' | b'\r' | b'\n' | 0x0C)) {
                self.pos += 1;
            }
            // line splice \\
            if self.starts_with("\\\n") {
                self.pos += 2;
                continue;
            }
            // comments
            if self.starts_with("//") {
                self.pos += 2;
                while let Some(c) = self.peek() {
                    self.pos += 1;
                    if c == b'\n' {
                        break;
                    }
                }
                continue;
            }
            if self.starts_with("/*") {
                self.pos += 2;
                while self.pos < self.len && !self.starts_with("*/") {
                    self.pos += 1;
                }
                if self.starts_with("*/") {
                    self.pos += 2;
                }
                continue;
            }
            break;
        }
    }

    pub fn next_token(&mut self) -> Option<Token> {
        self.skip_ws_and_comments();
        let start = self.pos;
        let c = self.peek()?;

        // Identifier or keyword
        if Self::is_ident_start(c) {
            self.bump();
            while let Some(c2) = self.peek() {
                if Self::is_ident_continue(c2) {
                    self.pos += 1;
                } else {
                    break;
                }
            }
            let lex = &self.src[start..self.pos];
            let kind = if let Some(kw) = to_keyword(lex) {
                K::Keyword(kw)
            } else {
                K::Identifier(lex.to_string())
            };
            return Some(Token {
                kind,
                span: self.make_span(start),
            });
        }

        // Number literal (simple C89 integer: dec/oct/hex; suffixes kept in repr)
        if (c as char).is_ascii_digit() {
            if self.starts_with("0x") || self.starts_with("0X") {
                self.pos += 2;
                while let Some(ch) = self.peek() {
                    if (ch as char).is_ascii_hexdigit() {
                        self.pos += 1;
                    } else {
                        break;
                    }
                }
                let repr = &self.src[start..self.pos];
                let kind = K::Literal(LiteralKind::Int {
                    base: IntBase::Hex,
                    repr: repr.to_string(),
                });
                return Some(Token {
                    kind,
                    span: self.make_span(start),
                });
            } else if c == b'0' {
                self.pos += 1;
                while let Some(ch) = self.peek() {
                    if (ch as char).is_ascii_digit() && ch != b'8' && ch != b'9' {
                        self.pos += 1;
                    } else {
                        break;
                    }
                }
                let repr = &self.src[start..self.pos];
                let kind = K::Literal(LiteralKind::Int {
                    base: IntBase::Oct,
                    repr: repr.to_string(),
                });
                return Some(Token {
                    kind,
                    span: self.make_span(start),
                });
            } else {
                self.pos += 1;
                while let Some(ch) = self.peek() {
                    if (ch as char).is_ascii_digit() {
                        self.pos += 1;
                    } else {
                        break;
                    }
                }
                let repr = &self.src[start..self.pos];
                let kind = K::Literal(LiteralKind::Int {
                    base: IntBase::Dec,
                    repr: repr.to_string(),
                });
                return Some(Token {
                    kind,
                    span: self.make_span(start),
                });
            }
        }

        // String literal
        if c == b'"' {
            self.bump();
            while let Some(ch) = self.bump() {
                match ch {
                    b'\\' => {
                        let _ = self.bump();
                    } // consume escaped char (rough)
                    b'"' => break,
                    _ => {}
                }
            }
            let repr = &self.src[start..self.pos];
            let kind = K::Literal(LiteralKind::String {
                repr: repr.to_string(),
            });
            return Some(Token {
                kind,
                span: self.make_span(start),
            });
        }

        // Char literal
        if c == b'\'' {
            self.bump();
            if let Some(ch) = self.bump() {
                if ch == b'\\' {
                    let _ = self.bump();
                } // escaped
            }
            let _ = self.bump(); // closing '
            let repr = &self.src[start..self.pos];
            let kind = K::Literal(LiteralKind::Char {
                repr: repr.to_string(),
            });
            return Some(Token {
                kind,
                span: self.make_span(start),
            });
        }

        // Punctuators/operators (prefer longest match)
        // Ellipsis
        if self.starts_with("...") {
            self.pos += 3;
            return Some(Token {
                kind: K::Punct(P::Ellipsis),
                span: self.make_span(start),
            });
        }

        // 3-char shifts assign
        if self.starts_with("<<=") {
            self.pos += 3;
            return Some(Token {
                kind: K::Punct(P::ShlAssign),
                span: self.make_span(start),
            });
        }
        if self.starts_with(">>=") {
            self.pos += 3;
            return Some(Token {
                kind: K::Punct(P::ShrAssign),
                span: self.make_span(start),
            });
        }

        // 2-char
        if self.starts_with("->") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::Arrow),
                span: self.make_span(start),
            });
        }
        if self.starts_with("++") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::Inc),
                span: self.make_span(start),
            });
        }
        if self.starts_with("--") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::Dec),
                span: self.make_span(start),
            });
        }
        if self.starts_with("<=") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::Le),
                span: self.make_span(start),
            });
        }
        if self.starts_with(">=") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::Ge),
                span: self.make_span(start),
            });
        }
        if self.starts_with("==") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::Eq),
                span: self.make_span(start),
            });
        }
        if self.starts_with("!=") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::Ne),
                span: self.make_span(start),
            });
        }
        if self.starts_with("&&") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::AndAnd),
                span: self.make_span(start),
            });
        }
        if self.starts_with("||") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::OrOr),
                span: self.make_span(start),
            });
        }
        if self.starts_with("+=") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::PlusAssign),
                span: self.make_span(start),
            });
        }
        if self.starts_with("-=") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::MinusAssign),
                span: self.make_span(start),
            });
        }
        if self.starts_with("*=") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::StarAssign),
                span: self.make_span(start),
            });
        }
        if self.starts_with("/=") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::SlashAssign),
                span: self.make_span(start),
            });
        }
        if self.starts_with("%=") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::PercentAssign),
                span: self.make_span(start),
            });
        }
        if self.starts_with("<<") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::Shl),
                span: self.make_span(start),
            });
        }
        if self.starts_with(">>") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::Shr),
                span: self.make_span(start),
            });
        }
        if self.starts_with("&=") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::AndAssign),
                span: self.make_span(start),
            });
        }
        if self.starts_with("|=") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::OrAssign),
                span: self.make_span(start),
            });
        }
        if self.starts_with("^=") {
            self.pos += 2;
            return Some(Token {
                kind: K::Punct(P::XorAssign),
                span: self.make_span(start),
            });
        }

        // 1-char
        let ch = self.bump().unwrap();
        let pk = match ch {
            b'(' => P::LParen,
            b')' => P::RParen,
            b'{' => P::LBrace,
            b'}' => P::RBrace,
            b'[' => P::LBracket,
            b']' => P::RBracket,
            b';' => P::Semicolon,
            b',' => P::Comma,
            b'.' => P::Dot,
            b'+' => P::Plus,
            b'-' => P::Minus,
            b'*' => P::Star,
            b'/' => P::Slash,
            b'%' => P::Percent,
            b'&' => P::Amp,
            b'|' => P::Pipe,
            b'^' => P::Caret,
            b'~' => P::Tilde,
            b'!' => P::Bang,
            b'?' => P::Question,
            b':' => P::Colon,
            b'=' => P::Assign,
            b'<' => P::Lt,
            b'>' => P::Gt,
            _ => {
                return Some(Token {
                    kind: K::Identifier((ch as char).to_string()),
                    span: self.make_span(start),
                });
            }
        };
        Some(Token {
            kind: K::Punct(pk),
            span: self.make_span(start),
        })
    }
}