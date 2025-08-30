use anyhow::{bail, Context, Result};
use lex::{Keyword as Kw, Lexer, LiteralKind, Punctuator as P, Token, TokenKind as K};
use std::collections::HashSet;

use crate::ast::*;

pub struct Parser {
    toks: Vec<Token>,
    pos: usize,
    // Scoped typedef-name tracking: each block introduces a new scope
    typedef_scopes: Vec<HashSet<String>>, // stack of typedef-names
    // New: accumulate record and enum definitions encountered while parsing types
    records: Vec<RecordDef>,
    enums: Vec<EnumDef>,
}

impl Parser {
    pub fn from_source(src: &str) -> Self {
        let mut lx = Lexer::new(src);
        let mut toks = Vec::new();
        while let Some(t) = lx.next_token() {
            toks.push(t);
        }
        Self { toks, pos: 0, typedef_scopes: vec![HashSet::new()], records: Vec::new(), enums: Vec::new() }
    }

    fn peek(&self) -> Option<&Token> { self.toks.get(self.pos) }
    fn bump(&mut self) -> Option<&Token> { let i = self.pos; self.pos += 1; self.toks.get(i) }

    fn peek_kind(&self) -> Option<K> { self.peek().map(|t| t.kind.clone()) }
    fn peek_kind_n(&self, n: usize) -> Option<K> { self.toks.get(self.pos + n).map(|t| t.kind.clone()) }

    fn expect_punct(&mut self, p: P) -> Result<()> {
        match self.bump().map(|t| &t.kind) {
            Some(K::Punct(pp)) if *pp == p => Ok(()),
            other => bail!("expected punct {:?}, got {:?}", p, other),
        }
    }

    fn consume_punct(&mut self, p: P) -> bool {
        if let Some(K::Punct(pp)) = self.peek().map(|t| &t.kind) {
            if *pp == p { self.pos += 1; return true; }
        }
        false
    }

    fn consume_keyword(&mut self, kw: Kw) -> bool {
        if let Some(K::Keyword(k)) = self.peek().map(|t| &t.kind) {
            if *k == kw { self.pos += 1; return true; }
        }
        false
    }

    fn expect_ident(&mut self) -> Result<String> {
        match self.bump().map(|t| &t.kind) {
            Some(K::Identifier(s)) => Ok(s.clone()),
            other => bail!("expected identifier, got {:?}", other),
        }
    }

    // Typedef-name environment helpers
    fn push_typedef_scope(&mut self) { self.typedef_scopes.push(HashSet::new()); }
    fn pop_typedef_scope(&mut self) { let _ = self.typedef_scopes.pop(); }
    fn insert_typedef(&mut self, name: String) { if let Some(s) = self.typedef_scopes.last_mut() { s.insert(name); } }
    fn is_typedef_name(&self, s: &str) -> bool {
        for sc in self.typedef_scopes.iter().rev() { if sc.contains(s) { return true; } }
        false
    }

    fn peek_is_type_name(&self) -> bool {
        match self.peek_kind() {
            Some(K::Keyword(kw)) => matches!(
                kw,
                Kw::Int | Kw::Void | Kw::Struct | Kw::Union | Kw::Enum
                    | Kw::Signed | Kw::Unsigned | Kw::Short | Kw::Long | Kw::Char
            ),
            Some(K::Identifier(ref s)) => self.is_typedef_name(s),
            _ => false,
        }
    }

    fn parse_type(&mut self) -> Result<Type> {
        // consume optional qualifiers (ignored for now)
        loop {
            if self.consume_keyword(Kw::Const) || self.consume_keyword(Kw::Volatile) { continue; }
            break;
        }

        // Accept C89 integer specifier sequences; track signedness and width
        let mut saw_any_int_spec = false;
        let mut saw_signed = false;
        let mut saw_unsigned = false;
        let mut count_short = 0usize;
        let mut count_long = 0usize;
        let mut saw_char = false;
        let mut saw_int_kw = false;
        loop {
            match self.peek_kind() {
                Some(K::Keyword(kw)) if matches!(kw, Kw::Signed | Kw::Unsigned | Kw::Short | Kw::Long | Kw::Char | Kw::Int) => {
                    self.pos += 1; // consume specifier
                    saw_any_int_spec = true;
                    match kw {
                        Kw::Signed => { saw_signed = true; }
                        Kw::Unsigned => { saw_unsigned = true; }
                        Kw::Short => { count_short = count_short.saturating_add(1); }
                        Kw::Long => { count_long = count_long.saturating_add(1); }
                        Kw::Char => { saw_char = true; }
                        Kw::Int => { saw_int_kw = true; }
                        _ => {}
                    }
                }
                _ => break,
            }
        }
        if saw_any_int_spec {
            // Map C89 integer specifier combinations to precise kinds.
            // Rules:
            // - 'char' with optional 'signed'/'unsigned'
            // - 'short' [int], 'long' [int]
            // - plain 'signed'/'unsigned' imply int
            if saw_char {
                let ty = if saw_unsigned { Type::UChar } else if saw_signed { Type::SChar } else { Type::Char };
                return Ok(ty);
            }
            if count_short > 0 {
                let ty = if saw_unsigned { Type::UShort } else { Type::Short };
                return Ok(ty);
            }
            if count_long > 0 {
                let ty = if saw_unsigned { Type::ULong } else { Type::Long };
                return Ok(ty);
            }
            // Default: int family
            let ty = if saw_unsigned { Type::UInt } else { Type::Int };
            return Ok(ty);
        }
        if self.consume_keyword(Kw::Void) { return Ok(Type::Void); }
        if self.consume_keyword(Kw::Struct) {
            let tag = if let Some(K::Identifier(name)) = self.peek_kind() { self.pos += 1; name } else { String::new() };
            let mut members_acc: Vec<(String, Type)> = Vec::new();
            if self.consume_punct(P::LBrace) {
                loop {
                    if self.consume_punct(P::RBrace) { break; }
                    let mut mty = self.parse_type()?;
                    while self.consume_punct(P::Star) { mty = Type::Pointer(Box::new(mty)); }
                    let mname = self.expect_ident()?;
                    self.expect_punct(P::Semicolon)?;
                    members_acc.push((mname, mty));
                }
                // Record the struct definition if there is a tag (empty tag allowed but less useful)
                self.records.push(RecordDef { kind: RecordKind::Struct, tag: tag.clone(), members: members_acc });
            }
            return Ok(Type::Struct(tag));
        }
        if self.consume_keyword(Kw::Union) {
            let tag = if let Some(K::Identifier(name)) = self.peek_kind() { self.pos += 1; name } else { String::new() };
            let mut members_acc: Vec<(String, Type)> = Vec::new();
            if self.consume_punct(P::LBrace) {
                loop {
                    if self.consume_punct(P::RBrace) { break; }
                    let mut mty = self.parse_type()?;
                    while self.consume_punct(P::Star) { mty = Type::Pointer(Box::new(mty)); }
                    let mname = self.expect_ident()?;
                    self.expect_punct(P::Semicolon)?;
                    members_acc.push((mname, mty));
                }
                self.records.push(RecordDef { kind: RecordKind::Union, tag: tag.clone(), members: members_acc });
            }
            return Ok(Type::Union(tag));
        }
        if self.consume_keyword(Kw::Enum) {
            let tag = if let Some(K::Identifier(name)) = self.peek_kind() { self.pos += 1; name } else { String::new() };
            if self.consume_punct(P::LBrace) {
                let mut enumerators: Vec<(String, Option<Expr>)> = Vec::new();
                loop {
                    if self.consume_punct(P::RBrace) { break; }
                    let name = match self.peek_kind() {
                        Some(K::Identifier(n)) => { self.pos += 1; n }
                        other => bail!("expected enumerator identifier, got {:?}", other),
                    };
                    let mut val_expr: Option<Expr> = None;
                    if self.consume_punct(P::Assign) {
                        match self.peek_kind() {
                            Some(K::Literal(LiteralKind::Int { repr, .. })) => { self.pos += 1; val_expr = Some(Expr::IntLiteral(repr)); }
                            other => bail!("expected integer literal after '=' in enum enumerator, got {:?}", other),
                        }
                    }
                    enumerators.push((name, val_expr));
                    let _ = self.consume_punct(P::Comma);
                }
                self.enums.push(EnumDef { tag: tag.clone(), enumerators });
            }
            return Ok(Type::Enum(tag));
        }
        // typedef-name as a type-specifier
        if let Some(K::Identifier(ref s)) = self.peek_kind() {
            if self.is_typedef_name(s) {
                let name = if let Some(K::Identifier(s2)) = self.bump().map(|t| t.kind.clone()) { s2 } else { unreachable!() };
                return Ok(Type::Named(name));
            }
        }

        bail!("expected type (int family, void, struct, union, enum, or typedef-name)")
    }
    fn parse_type_with_ptrs(&mut self) -> Result<Type> {
        let mut ty = self.parse_type()?;
        while self.consume_punct(P::Star) { ty = Type::Pointer(Box::new(ty)); }
        Ok(ty)
    }
    fn parse_params(&mut self) -> Result<(Vec<Param>, bool)> {
        // () or (void)
        if self.consume_punct(P::RParen) { return Ok((vec![], false)); }
        if self.consume_keyword(Kw::Void) { self.expect_punct(P::RParen)?; return Ok((vec![], false)); }

        // Disallow leading ellipsis (must have at least one named parameter before ...)
        if let Some(K::Punct(P::Ellipsis)) = self.peek_kind() { bail!("ellipsis requires at least one named parameter before it"); }

        let mut params = Vec::new();
        let mut variadic = false;
        loop {
            let mut ty = self.parse_type()?;
            while self.consume_punct(P::Star) { ty = Type::Pointer(Box::new(ty)); }
            let name = self.expect_ident()?;
            params.push(Param { name, ty });

            // Comma: either another parameter or a trailing ellipsis
            if self.consume_punct(P::Comma) {
                if let Some(K::Punct(P::Ellipsis)) = self.peek_kind() {
                    // Trailing ellipsis must be last, require closing ')'
                    self.pos += 1; // consume '...'
                    self.expect_punct(P::RParen)?;
                    variadic = true;
                    return Ok((params, variadic));
                }
                // Otherwise, continue parsing next named parameter
                continue;
            }
            // No comma: we must be at the closing ')'
            self.expect_punct(P::RParen)?;
            break;
            break;
        }
        Ok((params, variadic))
    }

    // New: parse a parameter type list (without names) for declarators
    fn parse_param_types_list(&mut self) -> Result<(Vec<Type>, bool)> {
        // () or (void)
        if self.consume_punct(P::RParen) { return Ok((vec![], false)); }
        if self.consume_keyword(Kw::Void) { self.expect_punct(P::RParen)?; return Ok((vec![], false)); }

        let mut params: Vec<Type> = Vec::new();
        let mut variadic = false;
        loop {
            // Trailing ellipsis allowed after at least one param
            if let Some(K::Punct(P::Ellipsis)) = self.peek_kind() {
                // consume '...'
                self.pos += 1;
                self.expect_punct(P::RParen)?;
                variadic = true;
                return Ok((params, variadic));
            }
            let mut ty = self.parse_type()?;
            while self.consume_punct(P::Star) { ty = Type::Pointer(Box::new(ty)); }
            params.push(ty);

            if self.consume_punct(P::Comma) {
                continue;
            }
            self.expect_punct(P::RParen)?;
            break;
        }
        Ok((params, variadic))
    }
        match self.peek_kind() {
            Some(K::Literal(LiteralKind::Int { repr, .. })) => { self.pos += 1; Ok(Expr::IntLiteral(repr)) }
            Some(K::Literal(LiteralKind::String { repr })) => { self.pos += 1; Ok(Expr::StringLiteral(repr)) }
            Some(K::Literal(LiteralKind::Char { repr })) => { self.pos += 1; let v = decode_char_literal(&repr); Ok(Expr::IntLiteral(format!("{}", v))) }
            Some(K::Identifier(s)) => { self.pos += 1; Ok(Expr::Ident(s)) }
            Some(K::Punct(P::LParen)) => { self.pos += 1; let e = self.parse_expr()?; self.expect_punct(P::RParen)?; Ok(e) }
            Some(other) => bail!("unexpected token in primary: {:?}", other),
            None => bail!("unexpected EOF in primary"),
        }
    }

    // Postfix: calls ident(...), postfix ++/--, indexing expr[expr], member access expr.field / expr->field
    fn parse_postfix(&mut self) -> Result<Expr> {
        let mut e = self.parse_primary_base()?;
        loop {
            match self.peek_kind() {
                Some(K::Punct(P::LParen)) => {
                    // Function call: ident(...) -> Expr::Call; otherwise treat as function-pointer call Expr::CallPtr
                    self.pos += 1; // '('
                    let mut args = Vec::new();
                    if !self.consume_punct(P::RParen) {
                        loop {
                            let a = self.parse_assignment()?;
                            args.push(a);
                            if self.consume_punct(P::Comma) { continue; }
                            self.expect_punct(P::RParen)?;
                            break;
                        }
                    }
                    let e_new = match e {
                        Expr::Ident(ref name) => {
                            let callee = name.clone();
                            Expr::Call { callee, args }
                        }
                        other => {
                            Expr::CallPtr { target: Box::new(other), args }
                        }
                    };
                    e = e_new;
                }
                Some(K::Punct(P::Inc)) => { self.pos += 1; e = Expr::IncDec { pre: false, inc: true,  target: Box::new(e) }; }
                Some(K::Punct(P::Dec)) => { self.pos += 1; e = Expr::IncDec { pre: false, inc: false, target: Box::new(e) }; }
                Some(K::Punct(P::LBracket)) => { self.pos += 1; let idx = self.parse_expr()?; self.expect_punct(P::RBracket)?; e = Expr::Index { base: Box::new(e), index: Box::new(idx) }; }
                Some(K::Punct(P::Dot)) => { self.pos += 1; let field = self.expect_ident()?; e = Expr::Member { base: Box::new(e), field, arrow: false }; }
                Some(K::Punct(P::Arrow)) => { self.pos += 1; let field = self.expect_ident()?; e = Expr::Member { base: Box::new(e), field, arrow: true }; }
                _ => break,
            }
        }
        Ok(e)
    }

    fn parse_unary(&mut self) -> Result<Expr> {
        if let Some(K::Keyword(Kw::Sizeof)) = self.peek_kind() {
            self.pos += 1; // sizeof
            if self.consume_punct(P::LParen) {
                let is_type = self.peek_is_type_name();
                if is_type {
                    let ty = self.parse_type_with_ptrs()?;
                    self.expect_punct(P::RParen)?;
                    return Ok(Expr::SizeofType(ty));
                } else {
                    let e = self.parse_expr()?;
                    self.expect_punct(P::RParen)?;
                    return Ok(Expr::SizeofExpr(Box::new(e)));
                }
            } else {
                let e = self.parse_unary()?;
                return Ok(Expr::SizeofExpr(Box::new(e)));
            }
        }
        // Cast: (type) unary
        if let Some(K::Punct(P::LParen)) = self.peek_kind() {
            let next_is_type = match self.peek_kind_n(1) {
                Some(K::Keyword(kw)) => matches!(kw, Kw::Int | Kw::Void | Kw::Struct | Kw::Union | Kw::Enum | Kw::Signed | Kw::Unsigned | Kw::Short | Kw::Long | Kw::Char),
                Some(K::Identifier(ref s)) => self.is_typedef_name(s),
                _ => false,
            };
            if next_is_type {
                self.pos += 1; // '('
                let ty = self.parse_type_with_ptrs()?;
                self.expect_punct(P::RParen)?;
                let e = self.parse_unary()?;
                return Ok(Expr::Cast { ty, expr: Box::new(e) });
            }
        }
        match self.peek_kind() {
            Some(K::Punct(P::Inc))   => { self.pos += 1; Ok(Expr::IncDec { pre: true, inc: true,  target: Box::new(self.parse_unary()?) }) }
            Some(K::Punct(P::Dec))   => { self.pos += 1; Ok(Expr::IncDec { pre: true, inc: false, target: Box::new(self.parse_unary()?) }) }
            Some(K::Punct(P::Plus))  => { self.pos += 1; Ok(Expr::Unary { op: UnaryOp::Plus,  expr: Box::new(self.parse_unary()?) }) }
            Some(K::Punct(P::Minus)) => { self.pos += 1; Ok(Expr::Unary { op: UnaryOp::Minus, expr: Box::new(self.parse_unary()?) }) }
            Some(K::Punct(P::Tilde)) => { self.pos += 1; Ok(Expr::Unary { op: UnaryOp::BitNot, expr: Box::new(self.parse_unary()?) }) }
            Some(K::Punct(P::Bang))  => { self.pos += 1; Ok(Expr::Unary { op: UnaryOp::LogicalNot, expr: Box::new(self.parse_unary()?) }) }
            Some(K::Punct(P::Amp))   => { self.pos += 1; Ok(Expr::Unary { op: UnaryOp::AddrOf,     expr: Box::new(self.parse_unary()?) }) }
            Some(K::Punct(P::Star))  => { self.pos += 1; Ok(Expr::Unary { op: UnaryOp::Deref,      expr: Box::new(self.parse_unary()?) }) }
            _ => self.parse_postfix(),
        }
    }

    fn parse_mul_div_mod(&mut self) -> Result<Expr> {
        let mut lhs = self.parse_unary()?;
        loop {
            match self.peek_kind() {
                Some(K::Punct(P::Star))    => { self.pos += 1; let rhs = self.parse_unary()?; lhs = Expr::Binary { op: BinaryOp::Mul, lhs: Box::new(lhs), rhs: Box::new(rhs) }; }
                Some(K::Punct(P::Slash))   => { self.pos += 1; let rhs = self.parse_unary()?; lhs = Expr::Binary { op: BinaryOp::Div, lhs: Box::new(lhs), rhs: Box::new(rhs) }; }
                Some(K::Punct(P::Percent)) => { self.pos += 1; let rhs = self.parse_unary()?; lhs = Expr::Binary { op: BinaryOp::Mod, lhs: Box::new(lhs), rhs: Box::new(rhs) }; }
                _ => break,
            }
        }
        Ok(lhs)
    }

    fn parse_add_sub(&mut self) -> Result<Expr> {
        let mut lhs = self.parse_mul_div_mod()?;
        loop {
            match self.peek_kind() {
                Some(K::Punct(P::Plus))  => { self.pos += 1; let rhs = self.parse_mul_div_mod()?; lhs = Expr::Binary { op: BinaryOp::Plus,  lhs: Box::new(lhs), rhs: Box::new(rhs) }; }
                Some(K::Punct(P::Minus)) => { self.pos += 1; let rhs = self.parse_mul_div_mod()?; lhs = Expr::Binary { op: BinaryOp::Minus, lhs: Box::new(lhs), rhs: Box::new(rhs) }; }
                _ => break,
            }
        }
        Ok(lhs)
    }

    fn parse_shift(&mut self) -> Result<Expr> {
        let mut lhs = self.parse_add_sub()?;
        loop {
            match self.peek_kind() {
                Some(K::Punct(P::Shl)) => { self.pos += 1; let rhs = self.parse_add_sub()?; lhs = Expr::Binary { op: BinaryOp::Shl, lhs: Box::new(lhs), rhs: Box::new(rhs) }; }
                Some(K::Punct(P::Shr)) => { self.pos += 1; let rhs = self.parse_add_sub()?; lhs = Expr::Binary { op: BinaryOp::Shr, lhs: Box::new(lhs), rhs: Box::new(rhs) }; }
                _ => break,
            }
        }
        Ok(lhs)
    }

    fn parse_relational(&mut self) -> Result<Expr> {
        let mut lhs = self.parse_shift()?;
        loop {
            match self.peek_kind() {
                Some(K::Punct(P::Lt)) =>  { self.pos += 1; let rhs = self.parse_shift()?; lhs = Expr::Binary { op: BinaryOp::Lt, lhs: Box::new(lhs), rhs: Box::new(rhs) }; }
                Some(K::Punct(P::Le)) =>  { self.pos += 1; let rhs = self.parse_shift()?; lhs = Expr::Binary { op: BinaryOp::Le, lhs: Box::new(lhs), rhs: Box::new(rhs) }; }
                Some(K::Punct(P::Gt)) =>  { self.pos += 1; let rhs = self.parse_shift()?; lhs = Expr::Binary { op: BinaryOp::Gt, lhs: Box::new(lhs), rhs: Box::new(rhs) }; }
                Some(K::Punct(P::Ge)) =>  { self.pos += 1; let rhs = self.parse_shift()?; lhs = Expr::Binary { op: BinaryOp::Ge, lhs: Box::new(lhs), rhs: Box::new(rhs) }; }
                _ => break,
            }
        }
        Ok(lhs)
    }

    fn parse_equality(&mut self) -> Result<Expr> {
        let mut lhs = self.parse_relational()?;
        loop {
            match self.peek_kind() {
                Some(K::Punct(P::Eq)) => { self.pos += 1; let rhs = self.parse_relational()?; lhs = Expr::Binary { op: BinaryOp::Eq, lhs: Box::new(lhs), rhs: Box::new(rhs) }; }
                Some(K::Punct(P::Ne)) => { self.pos += 1; let rhs = self.parse_relational()?; lhs = Expr::Binary { op: BinaryOp::Ne, lhs: Box::new(lhs), rhs: Box::new(rhs) }; }
                _ => break,
            }
        }
        Ok(lhs)
    }

    fn parse_bitand(&mut self) -> Result<Expr> {
        let mut lhs = self.parse_equality()?;
        while self.consume_punct(P::Amp) {
            let rhs = self.parse_equality()?;
            lhs = Expr::Binary { op: BinaryOp::BitAnd, lhs: Box::new(lhs), rhs: Box::new(rhs) };
        }
        Ok(lhs)
    }

    fn parse_bitxor(&mut self) -> Result<Expr> {
        let mut lhs = self.parse_bitand()?;
        while self.consume_punct(P::Caret) {
            let rhs = self.parse_bitand()?;
            lhs = Expr::Binary { op: BinaryOp::BitXor, lhs: Box::new(lhs), rhs: Box::new(rhs) };
        }
        Ok(lhs)
    }

    fn parse_bitor(&mut self) -> Result<Expr> {
        let mut lhs = self.parse_bitxor()?;
        while self.consume_punct(P::Pipe) {
            let rhs = self.parse_bitxor()?;
            lhs = Expr::Binary { op: BinaryOp::BitOr, lhs: Box::new(lhs), rhs: Box::new(rhs) };
        }
        Ok(lhs)
    }

    fn parse_logical_and(&mut self) -> Result<Expr> {
        let mut lhs = self.parse_bitor()?;
        while let Some(K::Punct(P::AndAnd)) = self.peek_kind() {
            self.pos += 1;
            let rhs = self.parse_bitor()?;
            lhs = Expr::Binary { op: BinaryOp::LAnd, lhs: Box::new(lhs), rhs: Box::new(rhs) };
        }
        Ok(lhs)
    }

    fn parse_logical_or(&mut self) -> Result<Expr> {
        let mut lhs = self.parse_logical_and()?;
        while let Some(K::Punct(P::OrOr)) = self.peek_kind() {
            self.pos += 1;
            let rhs = self.parse_logical_and()?;
            lhs = Expr::Binary { op: BinaryOp::LOr, lhs: Box::new(lhs), rhs: Box::new(rhs) };
        }
        Ok(lhs)
    }

    fn parse_conditional(&mut self) -> Result<Expr> {
        let cond = self.parse_logical_or()?;
        if self.consume_punct(P::Question) {
            let then_e = self.parse_expr()?;
            self.expect_punct(P::Colon)?;
            let else_e = self.parse_conditional()?; // right-assoc
            Ok(Expr::Cond { cond: Box::new(cond), then_e: Box::new(then_e), else_e: Box::new(else_e) })
        } else {
            Ok(cond)
        }
    }

    fn punct_to_assign_binop(p: &P) -> Option<BinaryOp> {
        Some(match p {
            P::PlusAssign => BinaryOp::Plus,
            P::MinusAssign => BinaryOp::Minus,
            P::StarAssign => BinaryOp::Mul,
            P::SlashAssign => BinaryOp::Div,
            P::PercentAssign => BinaryOp::Mod,
            P::ShlAssign => BinaryOp::Shl,
            P::ShrAssign => BinaryOp::Shr,
            P::AndAssign => BinaryOp::BitAnd,
            P::OrAssign  => BinaryOp::BitOr,
            P::XorAssign => BinaryOp::BitXor,
            _ => return None,
        })
    }

    fn parse_assignment(&mut self) -> Result<Expr> {
        let save = self.pos;
        let lhs_try = self.parse_unary();
        if let Ok(lhs) = lhs_try {
            if let Some(K::Punct(p)) = self.peek_kind() {
                if p == P::Assign {
                    self.pos += 1; // '='
                    let rhs = self.parse_assignment()?; // right-assoc
                    return match lhs {
                        Expr::Ident(name) => Ok(Expr::Assign { name, value: Box::new(rhs) }),
                        Expr::Unary { op: UnaryOp::Deref, expr } => Ok(Expr::AssignDeref { ptr: expr, value: Box::new(rhs) }),
                        Expr::Index { base, index } => {
                            let ptr_expr = Expr::Binary { op: BinaryOp::Plus, lhs: base, rhs: index };
                            Ok(Expr::AssignDeref { ptr: Box::new(ptr_expr), value: Box::new(rhs) })
                        }
                        Expr::Member { base, field, arrow } => {
                            let member_expr = Expr::Member { base, field, arrow };
                            let addr = Expr::Unary { op: UnaryOp::AddrOf, expr: Box::new(member_expr) };
                            Ok(Expr::AssignDeref { ptr: Box::new(addr), value: Box::new(rhs) })
                        }
                        other => bail!("invalid assignment target: {:?}", other),
                    };
                } else if let Some(op) = Self::punct_to_assign_binop(&p) {
                    self.pos += 1; // op=
                    let rhs = self.parse_assignment()?; // right-assoc
                    return Ok(match lhs {
                        Expr::Index { base, index } => {
                            let ptr_expr = Expr::Binary { op: BinaryOp::Plus, lhs: base, rhs: index };
                            Expr::AssignOp { op, lhs: Box::new(Expr::Unary { op: UnaryOp::Deref, expr: Box::new(ptr_expr) }), rhs: Box::new(rhs) }
                        }
                        Expr::Member { base, field, arrow } => {
                            let member_expr = Expr::Member { base, field, arrow };
                            let deref_target = Expr::Unary { op: UnaryOp::Deref, expr: Box::new(Expr::Unary { op: UnaryOp::AddrOf, expr: Box::new(member_expr) }) };
                            Expr::AssignOp { op, lhs: Box::new(deref_target), rhs: Box::new(rhs) }
                        }
                        other => Expr::AssignOp { op, lhs: Box::new(other), rhs: Box::new(rhs) },
                    });
                }
            }
            self.pos = save;
        } else {
            self.pos = save;
        }
        self.parse_conditional()
    }

    // Lowest precedence, left-associative comma operator
    fn parse_comma(&mut self) -> Result<Expr> {
        let mut e = self.parse_assignment()?;
        while self.consume_punct(P::Comma) {
            let rhs = self.parse_assignment()?;
            e = Expr::Comma { lhs: Box::new(e), rhs: Box::new(rhs) };
        }
        Ok(e)
    }

    fn parse_expr(&mut self) -> Result<Expr> { self.parse_comma() }

    fn parse_block(&mut self) -> Result<Vec<Stmt>> {
        self.expect_punct(P::LBrace)?;
        self.push_typedef_scope();
        let mut items = Vec::new();
        while !self.consume_punct(P::RBrace) {
            items.push(self.parse_stmt()?);
        }
        self.pop_typedef_scope();
        Ok(items)
    }

    fn parse_stmt_or_block(&mut self) -> Result<Vec<Stmt>> {
        if let Some(K::Punct(P::LBrace)) = self.peek().map(|t| &t.kind) {
            self.parse_block()
        } else {
            Ok(vec![self.parse_stmt()?])
        }
    }

    fn parse_switch_body(&mut self) -> Result<Vec<Stmt>> {
        self.expect_punct(P::LBrace)?;
        self.push_typedef_scope();
        let mut items = Vec::new();
        loop {
            if self.consume_punct(P::RBrace) { break; }
            if self.consume_keyword(Kw::Case) {
                let val = self.parse_expr()?;
                self.expect_punct(P::Colon)?;
                items.push(Stmt::Case { value: val });
                continue;
            }
            if self.consume_keyword(Kw::Default) {
                self.expect_punct(P::Colon)?;
                items.push(Stmt::Default);
                continue;
            }
            items.push(self.parse_stmt()?);
        }
        self.pop_typedef_scope();
        Ok(items)
    }

    fn parse_stmt(&mut self) -> Result<Stmt> {
        if self.consume_keyword(Kw::Return) {
            let e = self.parse_expr()?;
            self.expect_punct(P::Semicolon)?;
            return Ok(Stmt::Return(e));
        }
        if self.consume_keyword(Kw::If) {
            self.expect_punct(P::LParen)?;
            let cond = self.parse_expr()?;
            self.expect_punct(P::RParen)?;
            let then_branch = self.parse_stmt_or_block()?;
            let else_branch = if self.consume_keyword(Kw::Else) { Some(self.parse_stmt_or_block()?) } else { None };
            return Ok(Stmt::If { cond, then_branch, else_branch });
        }
        if self.consume_keyword(Kw::While) {
            self.expect_punct(P::LParen)?;
            let cond = self.parse_expr()?;
            self.expect_punct(P::RParen)?;
            let body = self.parse_stmt_or_block()?;
            return Ok(Stmt::While { cond, body });
        }
        if self.consume_keyword(Kw::Do) {
            let body = self.parse_stmt_or_block()?;
            if !self.consume_keyword(Kw::While) { bail!("expected 'while' after 'do' body"); }
            self.expect_punct(P::LParen)?;
            let cond = self.parse_expr()?;
            self.expect_punct(P::RParen)?;
            self.expect_punct(P::Semicolon)?;
            return Ok(Stmt::DoWhile { body, cond });
        if self.consume_keyword(Kw::Typedef) {
            let mut ty = self.parse_type()?;
            while self.consume_punct(P::Star) { ty = Type::Pointer(Box::new(ty)); }

            // Support function-pointer typedef: typedef T (*Name)(param-types);
            if self.consume_punct(P::LParen) {
                self.expect_punct(P::Star)?;
                let name = self.expect_ident()?;
                self.expect_punct(P::RParen)?;
                self.expect_punct(P::LParen)?;
                let (param_types, variadic) = self.parse_param_types_list()?; // consumes ')'
                let fn_ty = Type::Func { ret: Box::new(ty), params: param_types, variadic };
                let ty = Type::Pointer(Box::new(fn_ty));
                self.expect_punct(P::Semicolon)?;
                self.insert_typedef(name.clone());
                return Ok(Stmt::Typedef { name, ty });
            }

            let name = self.expect_ident()?;
            // Optional array declarators for typedef name: typedef int A[10][2];
            if self.consume_punct(P::LBracket) {
                let mut sizes: Vec<usize> = Vec::new();
                loop {
                    let sz = match self.peek_kind() {
                        Some(K::Literal(LiteralKind::Int { repr, .. })) => { let _ = self.bump(); repr.parse::<usize>().unwrap_or(0) }
                        other => bail!("expected integer literal array size, got {:?}", other),
                    };
                    self.expect_punct(P::RBracket)?;
                    sizes.push(sz);
                    if !self.consume_punct(P::LBracket) { break; }
                }
                for sz in sizes.into_iter().rev() { ty = Type::Array(Box::new(ty), sz); }
            }
            self.expect_punct(P::Semicolon)?;
            self.insert_typedef(name.clone());
            return Ok(Stmt::Typedef { name, ty });
        }
        let save = self.pos;
        // Accumulate storage and qualifiers for local declarations
        let mut storage: Option<Storage> = None;
        let mut quals = Qualifiers::none();
        loop {
            if self.consume_keyword(Kw::Extern) { storage = Some(Storage::Extern); continue; }
            if self.consume_keyword(Kw::Static) { storage = Some(Storage::Static); continue; }
            if self.consume_keyword(Kw::Const) { quals.is_const = true; continue; }
            if self.consume_keyword(Kw::Volatile) { quals.is_volatile = true; continue; }
            if self.consume_keyword(Kw::Register) || self.consume_keyword(Kw::Auto) { continue; }
            break;
        }
        if self.peek_is_type_name() {
            let mut ty = self.parse_type()?;
            while self.consume_punct(P::Star) { ty = Type::Pointer(Box::new(ty)); }
            if matches!(ty, Type::Struct(_) | Type::Union(_) | Type::Enum(_)) && self.consume_punct(P::Semicolon) {
                return Ok(Stmt::ExprStmt(Expr::IntLiteral("0".to_string())));
            }

            // Local function-pointer declaration support: int (*fp)(...);
            if self.consume_punct(P::LParen) {
                self.expect_punct(P::Star)?;
                let name = self.expect_ident()?;
                self.expect_punct(P::RParen)?;
                self.expect_punct(P::LParen)?;
                let (param_types, variadic) = self.parse_param_types_list()?;
                let ty = Type::Pointer(Box::new(Type::Func { ret: Box::new(ty), params: param_types, variadic }));
                let init = if self.consume_punct(P::Assign) { Some(self.parse_expr()?) } else { None };
                self.expect_punct(P::Semicolon)?;
                return Ok(Stmt::Decl { name, ty, init, storage, quals });
            }

            let name = self.expect_ident()?;
            // Support repeated array declarators a[...] [...]; build innermost first (right-to-left)
            if self.consume_punct(P::LBracket) {
                let mut sizes: Vec<usize> = Vec::new();
                loop {
                    let sz = match self.peek_kind() {
                        Some(K::Literal(LiteralKind::Int { repr, .. })) => { let _ = self.bump(); repr.parse::<usize>().unwrap_or(0) }
                        other => bail!("expected integer literal array size, got {:?}", other),
                    };
                    self.expect_punct(P::RBracket)?;
                    sizes.push(sz);
                    if !self.consume_punct(P::LBracket) { break; }
                }
                // Fold sizes from right to left to make the rightmost dimension the innermost
                for sz in sizes.into_iter().rev() { ty = Type::Array(Box::new(ty), sz); }
            }
            let init = if self.consume_punct(P::Assign) { Some(self.parse_expr()?) } else { None };
            self.expect_punct(P::Semicolon)?;
            return Ok(Stmt::Decl { name, ty, init, storage, quals });
        }
        // Fallback: treat IDENTIFIER (with optional '*') IDENTIFIER as a declaration
        // This allows parsing unknown typedef names (e.g., 'T x;') to be handled by sema.
        let after_quals_pos = self.pos;
        if let Some(K::Identifier(_)) = self.peek_kind() {
            // Lookahead: IDENTIFIER ('*')* IDENTIFIER -> plausible declaration
            let mut i = 1usize;
            while let Some(K::Punct(P::Star)) = self.peek_kind_n(i) { i += 1; }
            if matches!(self.peek_kind_n(i), Some(K::Identifier(_))) {
                // Parse as declaration with Type::Named(first_identifier)
                let tn = if let Some(K::Identifier(s)) = self.bump().map(|t| t.kind.clone()) { s } else { unreachable!() };
                let mut ty = Type::Named(tn);
                while self.consume_punct(P::Star) { ty = Type::Pointer(Box::new(ty)); }
                let name = self.expect_ident()?;
                if self.consume_punct(P::LBracket) {
                    let mut sizes: Vec<usize> = Vec::new();
                    loop {
                        let sz = match self.peek_kind() {
                            Some(K::Literal(LiteralKind::Int { repr, .. })) => { let _ = self.bump(); repr.parse::<usize>().unwrap_or(0) }
                            other => bail!("expected integer literal array size, got {:?}", other),
                        };
                        self.expect_punct(P::RBracket)?;
                        sizes.push(sz);
                        if !self.consume_punct(P::LBracket) { break; }
                    }
                    for sz in sizes.into_iter().rev() { ty = Type::Array(Box::new(ty), sz); }
                }
                let init = if self.consume_punct(P::Assign) { Some(self.parse_expr()?) } else { None };
                self.expect_punct(P::Semicolon)?;
                return Ok(Stmt::Decl { name, ty, init, storage, quals });
            } else {
                // Not a plausible declaration; restore to after qualifiers for expression parse
                self.pos = after_quals_pos;
            }
        }
        self.pos = save;
        let e = self.parse_expr()?;
        self.expect_punct(P::Semicolon)?;
        Ok(Stmt::ExprStmt(e))
    }
    fn parse_function(&mut self, ret_type: Type, name: String) -> Result<Function> {
        self.expect_punct(P::LParen)?;
        let (params, variadic) = self.parse_params()?;
        let body = self.parse_block()?;
        Ok(Function { name, ret_type, params, variadic, body, storage: None })
    }

    // New: parse a single top-level item (function definition or global declaration)
    fn parse_top_level_item(&mut self, functions: &mut Vec<Function>, globals: &mut Vec<Global>) -> Result<()> {
        // Consume optional storage-class specifiers and qualifiers
        let mut storage: Option<Storage> = None;
        let mut quals = Qualifiers::none();
        loop {
            if self.consume_keyword(Kw::Extern) { storage = Some(Storage::Extern); continue; }
            if self.consume_keyword(Kw::Static) { storage = Some(Storage::Static); continue; }
            if self.consume_keyword(Kw::Const) { quals.is_const = true; continue; }
            if self.consume_keyword(Kw::Volatile) { quals.is_volatile = true; continue; }
            if self.consume_keyword(Kw::Register) || self.consume_keyword(Kw::Auto) { continue; }
            break;
        }

        if !self.peek_is_type_name() { bail!("expected type at top level"); }

        let mut ty = self.parse_type()?;
        while self.consume_punct(P::Star) { ty = Type::Pointer(Box::new(ty)); }

        // Handle tag-only declarations like 'struct S;'
        if matches!(ty, Type::Struct(_) | Type::Union(_) | Type::Enum(_)) && self.consume_punct(P::Semicolon) { return Ok(()); }

        // Support global function-pointer declarator: T (*name)(params);
        if self.consume_punct(P::LParen) {
            self.expect_punct(P::Star)?;
            let name = self.expect_ident()?;
            self.expect_punct(P::RParen)?;
            self.expect_punct(P::LParen)?;
            let (param_types, variadic) = self.parse_param_types_list()?;
            let decl_ty = Type::Pointer(Box::new(Type::Func { ret: Box::new(ty), params: param_types, variadic }));
            self.expect_punct(P::Semicolon)?;
            globals.push(Global { name, ty: decl_ty, init: None, storage, quals });
            return Ok(());
        }

        let name = self.expect_ident()?;

        // Function definition or prototype if next is '('
        if let Some(K::Punct(P::LParen)) = self.peek_kind() {
            // Parse parameter list
            self.pos += 1; // '('
            let (params, variadic) = self.parse_params()?; // consumes ')'
            // If followed by ';' -> function prototype declaration (no body)
            if self.consume_punct(P::Semicolon) { return Ok(()); }
            // Otherwise expect a function body
            let body = self.parse_block()?;
            let func = Function { name, ret_type: ty, params, variadic, body, storage };
            functions.push(func);
            return Ok(());
        }

        // Optional array declarator
        if self.consume_punct(P::LBracket) {
            let sz = match self.peek_kind() {
                Some(K::Literal(LiteralKind::Int { repr, .. })) => { let _ = self.bump(); repr.parse::<usize>().unwrap_or(0) }
                other => bail!("expected integer literal array size, got {:?}", other),
            };
            self.expect_punct(P::RBracket)?;
            ty = Type::Array(Box::new(ty), sz);
        }

        // Optional initializer
        let init = if self.consume_punct(P::Assign) { Some(self.parse_expr()?) } else { None };
        self.expect_punct(P::Semicolon)?;
        globals.push(Global { name, ty, init, storage, quals });
        Ok(())
    }

    pub fn parse_translation_unit(&mut self) -> Result<TranslationUnit> {
        let mut functions: Vec<Function> = Vec::new();
        let mut globals: Vec<Global> = Vec::new();
        while let Some(tok) = self.peek() {
            // Allow and skip stray semicolons at top-level
            if matches!(tok.kind, K::Punct(P::Semicolon)) { self.pos += 1; continue; }
            // Attempt to parse a top-level item
            self.parse_top_level_item(&mut functions, &mut globals)?;
        }
        Ok(TranslationUnit { functions, records: self.records.clone(), enums: self.enums.clone(), globals })
    }
}

fn decode_char_literal(repr: &str) -> i32 {
    let bytes = repr.as_bytes();
    if bytes.len() >= 2 && bytes[0] == b'\'' && bytes[bytes.len() - 1] == b'\'' {
        let inner = &repr[1..repr.len() - 1];
        let mut chars = inner.chars();
        if let Some(c0) = chars.next() {
            if c0 == '\\' {
                let mut rest = chars;
                match rest.next() {
                    Some('n') => 10,
                    Some('r') => 13,
                    Some('t') => 9,
                    Some('0') => 0,
                    Some('\\') => 92,
                    Some('\'') => 39,
                    Some('"') => 34,
                    Some('a') => 7,
                    Some('b') => 8,
                    Some('f') => 12,
                    Some('v') => 11,
                    Some('x') => {
                        let hex: String = rest.collect();
                        let mut acc: i32 = 0;
                        for ch in hex.chars() {
                            let v = ch.to_digit(16);
                            if let Some(d) = v { acc = ((acc << 4) | (d as i32)) & 0xFF; } else { break; }
                        }
                        acc
                    }
                    Some(d @ '0'..='7') => {
                        let mut acc: i32 = (d as i32 - '0' as i32) & 0x7;
                        for _ in 0..2 {
                            if let Some(ch) = rest.next() {
                                if ch >= '0' && ch <= '7' { acc = ((acc << 3) | ((ch as i32 - '0' as i32) & 0x7)) & 0xFF; } else { break; }
                            } else { break; }
                        }
                        acc
                    }
                    Some(other) => other as i32,
                    None => 0,
                }
            } else {
                c0 as i32
            }
        } else { 0 }
    } else { 0 }
}

pub fn parse_translation_unit(src: &str) -> Result<TranslationUnit> {
    let mut p = Parser::from_source(src);
    p.parse_translation_unit().context("failed to parse translation unit")
}