#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntBase {
    Dec,
    Oct,
    Hex,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Keyword {
    Auto,
    Break,
    Case,
    Char,
    Const,
    Continue,
    Default,
    Do,
    Double,
    Else,
    Enum,
    Extern,
    Float,
    For,
    Goto,
    If,
    Int,
    Long,
    Register,
    Return,
    Short,
    Signed,
    Sizeof,
    Static,
    Struct,
    Switch,
    Typedef,
    Union,
    Unsigned,
    Void,
    Volatile,
    While,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Punctuator {
    LParen, RParen,
    LBrace, RBrace,
    LBracket, RBracket,
    Semicolon, Comma, Dot, Ellipsis,
    Arrow,
    Plus, Minus, Star, Slash, Percent,
    Inc, Dec,
    Amp, Pipe, Caret, Tilde, Bang,
    Question, Colon,
    Assign,
    PlusAssign, MinusAssign, StarAssign, SlashAssign, PercentAssign,
    Shl, Shr,
    ShlAssign, ShrAssign,
    Lt, Gt, Le, Ge, Eq, Ne,
    AndAnd, OrOr,
    AndAssign, OrAssign, XorAssign,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LiteralKind {
    Int { base: IntBase, repr: String },
    Char { repr: String },
    String { repr: String },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    Identifier(String),
    Keyword(Keyword),
    Literal(LiteralKind),
    Punct(Punctuator),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}