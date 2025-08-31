use anyhow::{anyhow, Result};
use parse::ast::*;
use std::collections::{HashMap, HashSet};

// Target assumptions (x86_64/Linux-like)
const SIZEOF_INT: usize = 4;
const SIZEOF_PTR: usize = 8;
const ALIGN_INT: usize = 4;
const ALIGN_PTR: usize = 8;

/// Public layout structures for records
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructLayout {
    pub size: usize,
    pub align: usize,
    pub members: HashMap<String, (usize, Type)>, // name -> (offset, type)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnionLayout {
    pub size: usize,
    pub align: usize,
    pub members: HashMap<String, Type>, // name -> type (offset always 0)
}

/// Return the size (in bytes) of a basic type known to the current frontend.
/// This will be extended as more C89 types are added (struct/union/arrays, etc.).
pub fn sizeof_type(ty: &Type) -> usize {
    match ty {
        // C89 integers
        Type::Char | Type::SChar | Type::UChar => 1,
        Type::Short | Type::UShort => 2,
        // Target assumption: int and long are 4 bytes in this project
        Type::Int | Type::UInt | Type::Long | Type::ULong => SIZEOF_INT,

        Type::Void => 0, // C89: sizeof(void) is invalid; sema should error later – keep 0 as a placeholder
        Type::Pointer(_) => SIZEOF_PTR,
        Type::Array(elem, n) => n.saturating_mul(sizeof_type(elem)),

        // Enums have int size on this target for now
        Type::Enum(_) => SIZEOF_INT,

        // Aggregates require precomputed layouts; 0 for incomplete here
        Type::Struct(_) | Type::Union(_) => 0,

        // Function types are not objects; sizeof(function) is invalid; keep 0 as placeholder
        Type::Func { .. } => 0,

        // typedef-name placeholder until resolved
        Type::Named(_) => SIZEOF_INT,
    }
}

/// Return alignment (in bytes) of a type.
pub fn alignof_type(ty: &Type) -> usize {
    match ty {
        // C89 integers
        Type::Char | Type::SChar | Type::UChar => 1,
        Type::Short | Type::UShort => 2,
        // int/long align to 4 on this target
        Type::Int | Type::UInt | Type::Long | Type::ULong => ALIGN_INT,

        Type::Void => 1, // arbitrary; void as an object type is invalid
        Type::Pointer(_) => ALIGN_PTR,
        Type::Array(elem, _n) => alignof_type(elem),

        // Enums align as ints
        Type::Enum(_) => ALIGN_INT,

        // Aggregates: default to int alignment unless layout computed elsewhere
        Type::Struct(_) | Type::Union(_) => ALIGN_INT,

        // Function types are not objects; choose minimal alignment placeholder
        Type::Func { .. } => 1,

        // typedef-name placeholder
        Type::Named(_) => ALIGN_INT,
    }
}

fn is_integer(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Char
            | Type::SChar
            | Type::UChar
            | Type::Short
            | Type::UShort
            | Type::Int
            | Type::UInt
            | Type::Long
            | Type::ULong
            | Type::Enum(_)
    )
}

fn is_pointer(ty: &Type) -> bool {
    matches!(ty, Type::Pointer(_))
}

fn is_char_type(ty: &Type) -> bool {
    matches!(ty, Type::Char | Type::SChar | Type::UChar)
}

/// Integer promotions and usual arithmetic conversions for 32-bit int/long model
fn int_width(ty: &Type) -> u32 {
    match ty {
        Type::Char | Type::SChar | Type::UChar => 8,
        Type::Short | Type::UShort => 16,
        Type::Int | Type::UInt | Type::Long | Type::ULong | Type::Enum(_) => 32,
        _ => 0,
    }
}

fn is_signed_ty(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Char | Type::SChar | Type::Short | Type::Int | Type::Long | Type::Enum(_)
    )
}

fn integer_promotion(ty: &Type) -> Option<Type> {
    if !is_integer(ty) {
        return None;
    }
    // On this target, all narrow integer types promote to int
    if int_width(ty) < 32 {
        return Some(Type::Int);
    }
    Some(ty.clone())
}

/// Apply usual arithmetic conversions after integer promotions.
fn usual_arith_conv(a: &Type, b: &Type) -> Option<Type> {
    if !is_integer(a) || !is_integer(b) {
        return None;
    }
    let a = integer_promotion(a).unwrap();
    let b = integer_promotion(b).unwrap();
    if a == b {
        return Some(a);
    }
    use Type::*;

    // If either is unsigned long, result is unsigned long
    if matches!(a, ULong) || matches!(b, ULong) {
        return Some(ULong);
    }

    match (&a, &b) {
        // long vs unsigned int (both 32-bit here) -> unsigned long
        (Long, UInt) | (UInt, Long) => Some(ULong),
        // long vs int -> long
        (Long, Int) | (Int, Long) => Some(Long),
        // uint vs int -> uint
        (UInt, Int) | (Int, UInt) => Some(UInt),
        // other combos that still involve ULong
        (ULong, Long) | (Long, ULong) => Some(ULong),
        (ULong, Int) | (Int, ULong) | (ULong, UInt) | (UInt, ULong) => Some(ULong),
        _ => {
            // After promotions, remaining cases are effectively Int/UInt/Long
            if is_signed_ty(&a) == is_signed_ty(&b) {
                // same signedness: pick wider rank; all 32-bit here so Int is fine
                Some(Int)
            } else {
                // different signedness, same width -> unsigned wins
                Some(UInt)
            }
        }
    }
}

/// Public helpers for usual arithmetic conversions and conditional operator result type.
pub fn arith_result_type(a: &Type, b: &Type) -> Option<Type> {
    usual_arith_conv(a, b)
}

pub fn cond_result_type(t_then: &Type, t_else: &Type) -> Option<Type> {
    if is_integer(t_then) && is_integer(t_else) {
        usual_arith_conv(t_then, t_else)
    } else {
        None
    }
}

/// Public: return the promoted integer type (for shifts and tests)
pub fn promoted_int_type(t: &Type) -> Option<Type> {
    integer_promotion(t)
}

/// Public: shift result is the promoted left operand type
pub fn shift_result_lhs_promoted(lhs: &Type) -> Option<Type> {
    integer_promotion(lhs)
}

fn parse_int_literal_str(repr: &str) -> Option<i64> {
    if let Some(hex) = repr.strip_prefix("0x").or_else(|| repr.strip_prefix("0X")) {
        i64::from_str_radix(hex, 16).ok()
    } else if repr.len() > 1 && repr.starts_with('0') {
        // octal (fallback to decimal parse if empty after leading 0)
        i64::from_str_radix(&repr[1..], 8)
            .ok()
            .or_else(|| repr.parse::<i64>().ok())
    } else {
        repr.parse::<i64>().ok()
    }
}

fn eval_int_const_expr(e: &Expr) -> Option<i64> {
    match e {
        Expr::IntLiteral(s) => parse_int_literal_str(s),
        Expr::Unary {
            op: UnaryOp::Minus,
            expr,
        } => eval_int_const_expr(expr).map(|v| -v),
        Expr::Unary {
            op: UnaryOp::Plus,
            expr,
        } => eval_int_const_expr(expr),
        // Allow simple casts to int of a const int
        Expr::Cast {
            ty: Type::Int,
            expr,
        } => eval_int_const_expr(expr),
        _ => None,
    }
}

fn round_up(x: usize, a: usize) -> usize {
    if a == 0 {
        x
    } else {
        (x + a - 1) / a * a
    }
}

fn size_of_field(ty: &Type) -> usize {
    sizeof_type(ty)
}
fn align_of_field(ty: &Type) -> usize {
    alignof_type(ty)
}

fn build_struct_layout(members: &[(String, Type)]) -> StructLayout {
    let mut off = 0usize;
    let mut max_align = 1usize;
    let mut map: HashMap<String, (usize, Type)> = HashMap::new();
    for (name, ty) in members {
        let a = align_of_field(ty);
        let s = size_of_field(ty);
        max_align = max_align.max(a);
        off = round_up(off, a);
        map.insert(name.clone(), (off, ty.clone()));
        off = off.saturating_add(s);
    }
    let size = round_up(off, max_align.max(1));
    StructLayout {
        size,
        align: max_align.max(1),
        members: map,
    }
}

fn build_union_layout(members: &[(String, Type)]) -> UnionLayout {
    let mut size = 0usize;
    let mut max_align = 1usize;
    let mut map: HashMap<String, Type> = HashMap::new();
    for (name, ty) in members {
        let a = align_of_field(ty);
        let s = size_of_field(ty);
        max_align = max_align.max(a);
        size = size.max(s);
        map.insert(name.clone(), ty.clone());
    }
    let size = round_up(size, max_align.max(1));
    UnionLayout {
        size,
        align: max_align.max(1),
        members: map,
    }
}

/// Build record layouts from a TranslationUnit's collected record definitions.
pub fn build_record_layouts(
    tu: &TranslationUnit,
) -> (HashMap<String, StructLayout>, HashMap<String, UnionLayout>) {
    let mut structs: HashMap<String, StructLayout> = HashMap::new();
    let mut unions: HashMap<String, UnionLayout> = HashMap::new();
    for r in &tu.records {
        match r.kind {
            RecordKind::Struct => {
                structs.insert(r.tag.clone(), build_struct_layout(&r.members));
            }
            RecordKind::Union => {
                unions.insert(r.tag.clone(), build_union_layout(&r.members));
            }
        }
    }
    (structs, unions)
}

/// Compute enum constant values from TU; returns mapping enumerator name -> value.
pub fn compute_enum_values(tu: &TranslationUnit) -> HashMap<String, i64> {
    let mut map = HashMap::new();
    for e in &tu.enums {
        let mut next = 0i64;
        for (name, val) in &e.enumerators {
            let v = match val {
                Some(ex) => {
                    let v = eval_int_const_expr(ex).unwrap_or(next);
                    next = v;
                    v
                }
                None => next,
            };
            map.insert(name.clone(), v);
            next = next.saturating_add(1);
        }
    }
    map
}

/// A minimal semantic analyzer with scoped symbol tables and basic type checks.
struct Sema {
    scopes: Vec<HashMap<String, Type>>, // block/function scopes
    // Typedef scope stack: separate namespace from variables
    typedef_scopes: Vec<HashMap<String, Type>>, // name -> resolved type
    // Record layouts and enums for typing member access and sizeof in future
    struct_layouts: HashMap<String, StructLayout>,
    union_layouts: HashMap<String, UnionLayout>,
    enum_vals: HashMap<String, i64>,
    // New: global symbols (name -> type) for lookup within functions
    global_syms: HashMap<String, Type>,
    // New: function signatures: name -> (ret, params, variadic)
    func_sigs: HashMap<String, (Type, Vec<Type>, bool)>,
}

impl Sema {
    fn new() -> Self {
        Self {
            scopes: Vec::new(),
            typedef_scopes: Vec::new(),
            struct_layouts: HashMap::new(),
            union_layouts: HashMap::new(),
            enum_vals: HashMap::new(),
            global_syms: HashMap::new(),
            func_sigs: HashMap::new(),
        }
    }

    fn from_tu(tu: &TranslationUnit) -> Self {
        let (s, u) = build_record_layouts(tu);
        let e = compute_enum_values(tu);
        let mut me = Self {
            scopes: Vec::new(),
            typedef_scopes: Vec::new(),
            struct_layouts: s,
            union_layouts: u,
            enum_vals: e,
            global_syms: HashMap::new(),
            func_sigs: HashMap::new(),
        };
        me.populate_function_signatures(tu);
        me
    }

    fn populate_function_signatures(&mut self, tu: &TranslationUnit) {
        for f in &tu.functions {
            let params: Vec<Type> = f.params.iter().map(|p| p.ty.clone()).collect();
            self.func_sigs
                .insert(f.name.clone(), (f.ret_type.clone(), params, f.variadic));
        }
        // Built-ins used by tests/runtime
        // puts: int puts(char*) -> approximate as int*(ptr to int)
        self.func_sigs.entry("puts".to_string()).or_insert((
            Type::Int,
            vec![Type::Pointer(Box::new(Type::Int))],
            false,
        ));
        // printf: int printf(char*, ...) -> approximate as int*(ptr to int), variadic
        self.func_sigs.entry("printf".to_string()).or_insert((
            Type::Int,
            vec![Type::Pointer(Box::new(Type::Int))],
            true,
        ));
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
        self.typedef_scopes.push(HashMap::new());
    }
    fn pop_scope(&mut self) {
        let _ = self.scopes.pop();
        let _ = self.typedef_scopes.pop();
    }

    fn insert(&mut self, name: String, ty: Type) { if let Some(s) = self.scopes.last_mut() { s.insert(name, ty); } }

    fn lookup(&self, name: &str) -> Option<Type> {
        for s in self.scopes.iter().rev() {
            if let Some(t) = s.get(name) { return Some(t.clone()); }
        }
        if let Some(t) = self.global_syms.get(name) { return Some(t.clone()); }
        None
    }

    fn lookup_typedef(&self, name: &str) -> Option<Type> {
        for s in self.typedef_scopes.iter().rev() {
            if let Some(t) = s.get(name) { return Some(t.clone()); }
        }
        None
    }

    fn resolve_type_internal(&self, ty: &Type, seen: &mut HashSet<String>) -> Result<Type> {
        match ty {
            Type::Named(nm) => {
                if !seen.insert(nm.clone()) { return Err(anyhow!("cyclic typedef detected: {}", nm)); }
                let base = self.lookup_typedef(nm).ok_or_else(|| anyhow!("unknown typedef name: {}", nm))?;
                self.resolve_type_internal(&base, seen)
            }
            Type::Pointer(inner) => Ok(Type::Pointer(Box::new(self.resolve_type_internal(inner, seen)?))),
            Type::Array(inner, n) => Ok(Type::Array(Box::new(self.resolve_type_internal(inner, seen)?), *n)),
            other => Ok(other.clone()),
        }
    }

    fn resolve_type(&self, ty: &Type) -> Result<Type> {
        let mut seen: HashSet<String> = HashSet::new();
        self.resolve_type_internal(ty, &mut seen)
    }

    fn process_globals(&mut self, tu: &TranslationUnit) -> Result<()> {
        #[derive(Default)]
        struct Info { has_extern: bool, defs: usize, tentatives: usize }
        let mut map: HashMap<String, Info> = HashMap::new();
        let mut arr_sizes: HashMap<String, usize> = HashMap::new(); // name -> size (0 unsized)

        let is_incomplete_object = |this: &Sema, t: &Type| -> bool {
            match t {
                Type::Struct(tag) => !this.struct_layouts.contains_key(tag),
                Type::Union(tag)  => !this.union_layouts.contains_key(tag),
                Type::Array(inner, _n) => match &**inner {
                    Type::Struct(tag) => !this.struct_layouts.contains_key(tag),
                    Type::Union(tag)  => !this.union_layouts.contains_key(tag),
                    _ => false,
                },
                _ => false,
            }
        };

        for g in &tu.globals {
            let name = g.name.clone();
            let ty = g.ty.clone();
            let is_extern = matches!(g.storage, Some(Storage::Extern));
            let has_init = g.init.is_some();
            let rty = self.resolve_type(&ty)?;

            if is_extern && has_init { return Err(anyhow!("extern global '{}' cannot have initializer", name)); }

            if !is_extern {
                if is_incomplete_object(self, &rty) { return Err(anyhow!(format!("global object '{}' has incomplete type", name))); }
            }

            if let Some(init) = &g.init {
                if !self.is_const_initializer(&rty, init) { return Err(anyhow!("non-constant global initializer for {}", name)); }
                self.check_initializer(&rty, init)?;
            }

            if let Type::Array(_inner, n) = rty.clone() {
                let entry = arr_sizes.entry(name.clone()).or_insert(n);
                let prev = *entry;
                if prev == 0 { *entry = n; }
                else if n == 0 { /* keep prev */ }
                else if prev != n {
                    return Err(anyhow!(format!("conflicting array sizes for {}: {} vs {}", name, prev, n)));
                }
            }

            let entry = map.entry(name.clone()).or_default();
            if is_extern { entry.has_extern = true; }
            else if has_init { entry.defs = entry.defs.saturating_add(1); }
            else { entry.tentatives = entry.tentatives.saturating_add(1); }

            self.global_syms.entry(name).or_insert(ty);
        }

        for (name, info) in &map { if info.defs > 1 { return Err(anyhow!("duplicate global definition: {}", name)); } }
        Ok(())
    }

    fn estimate_c_string_len(repr: &str) -> usize {
        let bytes = repr.as_bytes();
        if bytes.len() < 2 || bytes[0] != b'"' || bytes[bytes.len()-1] != b'"' { return repr.len(); }
        let inner = &repr[1..repr.len()-1];
        let mut chars = inner.chars().peekable();
        let mut count = 0usize;
        while let Some(c) = chars.next() {
            if c == '\\' {
                if let Some(nc) = chars.peek().cloned() {
                    match nc {
                        'n'|'r'|'t'|'0'|'\\'|'\''|'"' => { let _=chars.next(); count+=1; continue; }
                        'x' => { let _=chars.next(); while let Some(h)=chars.peek().cloned(){ if h.is_ascii_hexdigit(){ let _=chars.next(); } else { break; } } count+=1; continue; }
                        '0'..='7' => { let _=chars.next(); for _ in 0..2 { if let Some(o)=chars.peek().cloned(){ if ('0'..='7').contains(&o){ let _=chars.next(); } else { break; } } } count+=1; continue; }
                        _ => { let _=chars.next(); count+=1; continue; }
                    }
                }
            }
            count += 1;
        }
        count
    }

    fn const_init_ok(&self, ty: &Type, e: &Expr) -> bool {
        let rty = match self.resolve_type(ty) { Ok(t) => t, Err(_) => return false };
        match rty {
            Type::Int | Type::UInt | Type::Long | Type::ULong | Type::Short | Type::UShort | Type::Char | Type::SChar | Type::UChar | Type::Enum(_) => {
                eval_int_const_expr(e).is_some()
            }
            Type::Pointer(ref inner) => match e {
                Expr::StringLiteral(_) => matches!(&**inner, Type::Int),
                Expr::Cast { ty: Type::Pointer(_), expr } => match expr.as_ref() {
                    Expr::StringLiteral(_) => matches!(&**inner, Type::Int),
                    Expr::IntLiteral(s) => parse_int_literal_str(s).map_or(false, |v| v == 0),
                    _ => false,
                },
                Expr::IntLiteral(s) => parse_int_literal_str(s).map_or(false, |v| v == 0),
                _ => false,
            },
            Type::Array(ref elem, n) => match e {
                Expr::StringLiteral(_s) => is_char_type(elem),
                Expr::InitList(items) => {
                    if n != 0 && items.len() > n { return false; }
                    for it in items {
                        if matches!(&**elem, Type::Array(_, _)) {
                            if let Expr::InitList(_) = it { if !self.const_init_ok(elem, it) { return false; } } else { return false; }
                        } else {
                            if eval_int_const_expr(it).is_none() { return false; }
                        }
                    }
                    true
                }
                _ => false,
            },
            Type::Struct(ref tag) => match e {
                Expr::InitList(items) => {
                    if let Some(s) = self.struct_layouts.get(tag) {
                        let mut members: Vec<(usize, Type)> = s.members.iter().map(|(_n,(off,t))| (*off, t.clone())).collect();
                        members.sort_by_key(|(o,_)| *o);
                        if items.len() > members.len() { return false; }
                        for it in items { if eval_int_const_expr(it).is_none() { return false; } }
                        true
                    } else { true }
                }
                _ => false,
            },
            _ => false,
        }
    }

    fn is_const_initializer(&self, ty: &Type, e: &Expr) -> bool { self.const_init_ok(ty, e) }

    fn check_tu(&mut self, tu: &TranslationUnit) -> Result<()> {
        self.process_globals(tu)?;
        for f in &tu.functions { self.check_function(f)?; }
        Ok(())
    }

    fn check_function(&mut self, f: &Function) -> Result<()> {
        self.push_scope();
        for p in &f.params { let rty = self.resolve_type(&p.ty)?; self.insert(p.name.clone(), rty); }
        self.check_block(&f.body)?;
        self.pop_scope();
        Ok(())
    }

    fn check_block(&mut self, body: &[Stmt]) -> Result<()> {
        self.push_scope();
        for s in body { self.check_stmt(s)?; }
        self.pop_scope();
        Ok(())
    }

    fn check_switch_body(&mut self, body: &[Stmt]) -> Result<()> {
        let mut seen_cases: HashSet<i64> = HashSet::new();
        let mut seen_default = false;
        for s in body {
            match s {
                Stmt::Case { value } => {
                    let v = eval_int_const_expr(value).ok_or_else(|| anyhow!("case label is not an integer constant"))?;
                    if !seen_cases.insert(v) { return Err(anyhow!("duplicate case label: {}", v)); }
                }
                Stmt::Default => {
                    if seen_default { return Err(anyhow!("multiple default labels in switch")); }
                    seen_default = true;
                }
                other => { self.check_stmt(other)?; }
            }
        }
        Ok(())
    }

    fn check_initializer(&mut self, ty: &Type, init: &Expr) -> Result<()> {
        let rty = self.resolve_type(ty)?;
        match rty {
            Type::Array(inner, n) => match init {
                Expr::StringLiteral(s) => {
                    if !is_char_type(&inner) { return Err(anyhow!("string literal not allowed for non-char array")); }
                    let len = Self::estimate_c_string_len(s);
                    if n == 0 || n >= len + 1 { Ok(()) } else { Err(anyhow!("char array initializer too small for string+NUL")) }
                }
                Expr::InitList(items) => {
                    if n != 0 && items.len() > n { return Err(anyhow!("too many initializers for array")); }
                    for it in items {
                        match (&*inner, it) {
                            (Type::Array(_, _), Expr::InitList(_)) => self.check_initializer(&inner, it)?,
                            (Type::Array(_, _), _) => { return Err(anyhow!("array element requires initializer list")); }
                            _ => {
                                let it_te = self.type_expr(it)?;
                                let at = self.resolve_type(&it_te)?;
                                if (is_integer(&inner) && is_integer(&at)) || (is_pointer(&inner) && is_pointer(&at)) { /* ok */ } else {
                                    return Err(anyhow!("incompatible initializer for array element"));
                                }
                            }
                        }
                    }
                    Ok(())
                }
                _ => Err(anyhow!("array initializer must be a braced list or string for char[]")),
            },
            Type::Struct(tag) => match init {
                Expr::InitList(items) => {
                    if let Some(s) = self.struct_layouts.get(&tag) {
                        let mut members: Vec<(usize, Type)> = s.members.iter().map(|(_n,(off,ty))| (*off, ty.clone())).collect();
                        members.sort_by_key(|(off, _)| *off);
                        if items.len() > members.len() { return Err(anyhow!("too many initializers for struct")); }
                        for (i, it) in items.iter().enumerate() {
                            if let Expr::InitList(_) = it { return Err(anyhow!("nested initializer for struct field {} not supported in v1", i+1)); }
                            let field_ty = &members[i].1;
                            let it_te = self.type_expr(it)?;
                            let at = self.resolve_type(&it_te)?;
                            if (is_integer(field_ty) && is_integer(&at)) || (is_pointer(field_ty) && is_pointer(&at)) { /* ok */ } else {
                                return Err(anyhow!("type mismatch in struct field {} initializer", i+1));
                            }
                        }
                        Ok(())
                    } else { Ok(()) }
                }
                _ => Err(anyhow!("struct initializer must be a braced list")),
            },
            _ => match init {
                Expr::InitList(_) => Err(anyhow!("scalar initializer cannot be a list")),
                e => {
                    let te = self.type_expr(e)?;
                    let at_raw = self.resolve_type(&te)?;
                    if let Type::Pointer(lhs_inner) = &rty {
                        if matches!(&**lhs_inner, Type::Func { .. }) {
                            if matches!(at_raw, Type::Func { .. }) { return Ok(()); }
                        }
                    }
                    let at = self.decay_array_to_ptr(&at_raw)?;
                    if is_pointer(&rty) && is_integer(&at) { if let Expr::IntLiteral(s) = e { if parse_int_literal_str(s).map_or(false, |v| v==0) { return Ok(()); } } }
                    if (is_integer(&rty) && is_integer(&at)) || (is_pointer(&rty) && is_pointer(&at)) { Ok(()) } else { Err(anyhow!("incompatible scalar initializer")) }
                }
            }
        }
    }

    fn check_stmt(&mut self, s: &Stmt) -> Result<()> {
        match s {
            Stmt::Block(stmts) => self.check_block(stmts),
            Stmt::If { cond, then_branch, else_branch } => { let _ = self.type_expr(cond)?; self.check_block(then_branch)?; if let Some(eb)=else_branch { self.check_block(eb)?; } Ok(()) }
            Stmt::While { cond, body } => { let _ = self.type_expr(cond)?; self.check_block(body) }
            Stmt::DoWhile { body, cond } => { let _ = self.type_expr(cond)?; self.check_block(body) }
            Stmt::For { init, cond, post, body } => {
                if let Some(i) = init { let _ = self.type_expr(i)?; }
                if let Some(c) = cond { let _ = self.type_expr(c)?; }
                if let Some(p) = post { let _ = self.type_expr(p)?; }
                self.check_block(body)
            }
            Stmt::Switch { cond, body } => { let ct = self.type_expr(cond)?; if !is_integer(&ct) { return Err(anyhow!("switch condition is not integer")); } self.check_switch_body(body) }
            Stmt::Case { .. } => Ok(()),
            Stmt::Default => Ok(()),
            Stmt::Break | Stmt::Continue => Ok(()),
            Stmt::Return(e) => { let _ = self.type_expr(e)?; Ok(()) }
            Stmt::Decl { name, ty, init, .. } => {
                let rty = self.resolve_type(ty)?;
                if !self.is_complete_object_type(&rty) { return Err(anyhow!("object of incomplete type")); }
                if let Some(e) = init { self.check_initializer(&rty, e)?; }
                self.insert(name.clone(), rty);
                Ok(())
            }
            Stmt::Typedef { name, ty } => {
                let rty = self.resolve_type(ty)?;
                if let Some(scope) = self.typedef_scopes.last_mut() {
                    if scope.contains_key(name) { return Err(anyhow!("redefinition of typedef {} in the same scope", name)); }
                    scope.insert(name.clone(), rty);
                    Ok(())
                } else { Err(anyhow!("typedef outside of any scope")) }
            }
            Stmt::Label(_name) => Ok(()),
            Stmt::Goto(_name) => Ok(()),
            Stmt::ExprStmt(e) => { let _ = self.type_expr(e)?; Ok(()) }
        }
    }

    fn decay_array_to_ptr(&self, t: &Type) -> Result<Type> {
        let r = self.resolve_type(t)?;
        match r { Type::Array(inner, _n) => Ok(Type::Pointer(inner)), other => Ok(other) }
    }

    fn is_complete_object_type(&self, ty: &Type) -> bool {
        let rty = match self.resolve_type(ty) { Ok(t) => t, Err(_) => return false };
        match rty {
            Type::Void => false,
            Type::Func { .. } => false,
            Type::Struct(ref tag) => self.struct_layouts.contains_key(tag),
            Type::Union(ref tag)  => self.union_layouts.contains_key(tag),
            Type::Array(ref inner, _n) => self.is_complete_object_type(inner),
            _ => true,
        }
    }

    fn type_compatible_for_param(&self, param: &Type, arg: &Type) -> Result<bool> {
        let p = self.resolve_type(param)?;
        let a = self.decay_array_to_ptr(arg)?;
        Ok((is_integer(&p) && is_integer(&a)) || (is_pointer(&p) && is_pointer(&a)))
    }

    fn is_null_pointer_constant_expr(e: &Expr) -> bool {
        match e {
            Expr::IntLiteral(s) => parse_int_literal_str(s).map_or(false, |v| v == 0),
            Expr::Cast { ty: Type::Pointer(_), expr } => match expr.as_ref() {
                Expr::IntLiteral(s) => parse_int_literal_str(s).map_or(false, |v| v == 0),
                _ => false,
            },
            _ => false,
        }
    }

    fn type_expr(&mut self, e: &Expr) -> Result<Type> {
        match e {
            Expr::Ident(name) => {
                if let Some(t) = self.lookup(name) { return Ok(t); }
                if let Some((ret, params, variadic)) = self.func_sigs.get(name).cloned() {
                    return Ok(Type::Func { ret: Box::new(ret), params, variadic });
                }
                Err(anyhow!("use of undeclared identifier: {}", name))
            }
            Expr::IntLiteral(_) => Ok(Type::Int),
            Expr::StringLiteral(_) => Ok(Type::Pointer(Box::new(Type::Int))),

            Expr::Unary { op, expr } => {
                let t = self.type_expr(expr)?;
                match op {
                    UnaryOp::Plus | UnaryOp::Minus | UnaryOp::BitNot | UnaryOp::LogicalNot => { let _ = self.resolve_type(&t)?; Ok(Type::Int) }
                    UnaryOp::AddrOf => { let rt = self.resolve_type(&t)?; Ok(Type::Pointer(Box::new(rt))) }
                    UnaryOp::Deref => { let rt = self.resolve_type(&t)?; if let Type::Pointer(inner) = rt { Ok(*inner) } else { Err(anyhow!("cannot dereference non-pointer")) } }
                }
            }

            Expr::Binary { op, lhs, rhs } => {
                let lt_raw = self.type_expr(lhs)?; let rt_raw = self.type_expr(rhs)?;
                let lt_res = self.resolve_type(&lt_raw)?; let rt_res = self.resolve_type(&rt_raw)?;
                let lt = match lt_res { Type::Array(inner, _) => Type::Pointer(inner), other => other };
                let rt = match rt_res { Type::Array(inner, _) => Type::Pointer(inner), other => other };
                use BinaryOp as B;
                match op {
                    B::Plus | B::Minus | B::Mul | B::Div | B::Mod | B::BitAnd | B::BitOr | B::BitXor => {
                        if matches!(op, B::Plus | B::Minus) {
                            match (&lt, &rt) {
                                (Type::Pointer(_), Type::Int) => return Ok(lt),
                                (Type::Int, Type::Pointer(_)) if matches!(op, B::Plus) => { return Ok(rt) }
                                (Type::Pointer(_), Type::Pointer(_)) if matches!(op, B::Minus) => { return Ok(Type::Int) }
                                _ => {}
                            }
                        }
                        usual_arith_conv(&lt, &rt).ok_or_else(|| anyhow!("invalid arithmetic between {:?} and {:?}", lt, rt))
                    }
                    B::Shl | B::Shr => { if !is_integer(&lt) || !is_integer(&rt) { return Err(anyhow!("invalid shift between {:?} and {:?}", lt, rt)); } promoted_int_type(&lt).ok_or_else(|| anyhow!("failed to promote shift lhs")) }
                    B::LAnd | B::LOr => Ok(Type::Int),
                    B::Lt | B::Le | B::Gt | B::Ge => { if usual_arith_conv(&lt, &rt).is_some() { Ok(Type::Int) } else { Err(anyhow!("invalid relational compare between {:?} and {:?}", lt, rt)) } }
                    B::Eq | B::Ne => { if (is_integer(&lt) && is_integer(&rt)) || (is_pointer(&lt) && is_pointer(&rt)) || (is_pointer(&lt) && is_integer(&rt)) || (is_integer(&lt) && is_pointer(&rt)) { Ok(Type::Int) } else { Err(anyhow!("invalid equality compare between {:?} and {:?}", lt, rt)) } }
                }
            }

            Expr::Assign { name, value } => {
                let val_te = self.type_expr(value)?; let vt = self.resolve_type(&val_te)?;
                let nt0 = self.lookup(name).ok_or_else(|| anyhow!("assignment to undeclared identifier: {}", name))?; let nt = self.resolve_type(&nt0)?;
                match (&nt, &vt) {
                    (Type::Struct(lt), Type::Struct(rt)) => {
                        if lt == rt { if self.struct_layouts.contains_key(lt) { Ok(nt) } else { Err(anyhow!("assignment involving incomplete struct {}", lt)) } }
                        else { Err(anyhow!("incompatible assignment to {}: {:?} = {:?}", name, nt, vt)) }
                    }
                    (Type::Union(lt), Type::Union(rt)) => {
                        if lt == rt { if self.union_layouts.contains_key(lt) { Ok(nt) } else { Err(anyhow!("assignment involving incomplete union {}", lt)) } }
                        else { Err(anyhow!("incompatible assignment to {}: {:?} = {:?}", name, nt, vt)) }
                    }
                    _ => { if (is_integer(&nt) && is_integer(&vt)) || (is_pointer(&nt) && is_pointer(&vt)) { Ok(nt) } else { Err(anyhow!("incompatible assignment to {}: {:?} = {:?}", name, nt, vt)) } }
                }
            }

            Expr::AssignDeref { ptr, value } => {
                let ptr_te = self.type_expr(ptr)?; let pt = self.resolve_type(&ptr_te)?;
                let val_te = self.type_expr(value)?; let vt = self.resolve_type(&val_te)?;
                match pt {
                    Type::Pointer(inner) => {
                        match &*inner {
                            Type::Struct(tag) => {
                                if !self.struct_layouts.contains_key(tag) { return Err(anyhow!("assignment involving incomplete struct {}", tag)); }
                                if let Type::Struct(rtag) = &vt { if rtag == tag { Ok(*inner) } else { Err(anyhow!("incompatible assignment through pointer to struct {}", tag)) } } else { Err(anyhow!("incompatible assignment through pointer to struct {}", tag)) }
                            }
                            Type::Union(tag) => {
                                if !self.union_layouts.contains_key(tag) { return Err(anyhow!("assignment involving incomplete union {}", tag)); }
                                if let Type::Union(rtag) = &vt { if rtag == tag { Ok(*inner) } else { Err(anyhow!("incompatible assignment through pointer to union {}", tag)) } } else { Err(anyhow!("incompatible assignment through pointer to union {}", tag)) }
                            }
                            _ => {
                                if is_integer(&*inner) && is_integer(&vt) { Ok(*inner) }
                                else if is_pointer(&*inner) && is_pointer(&vt) { Ok(*inner) }
                                else { Ok(*inner) }
                            }
                        }
                    }
                    _ => Err(anyhow!("cannot assign through non-pointer")),
                }
            }

            Expr::Call { callee, args } => {
                if let Some(vt) = self.lookup(callee) {
                    let t_callee = self.resolve_type(&vt)?;
                    let mut check_fn = |ret: Box<Type>, params: Vec<Type>, variadic: bool| -> Result<Type> {
                        if !variadic && args.len() != params.len() { return Err(anyhow!("arity mismatch in indirect call: expected {}, got {}", params.len(), args.len())); }
                        if variadic && args.len() < params.len() { return Err(anyhow!("too few arguments in indirect call: expected at least {}, got {}", params.len(), args.len())); }
                        for (i, pty) in params.iter().enumerate() {
                            let pty_res = self.resolve_type(pty)?;
                            if matches!(pty_res, Type::Pointer(_)) && Sema::is_null_pointer_constant_expr(&args[i]) { continue; }
                            let aty = self.type_expr(&args[i])?;
                            if !self.type_compatible_for_param(pty, &aty)? {
                                let rpt = self.resolve_type(pty)?; let rat = self.resolve_type(&aty)?;
                                return Err(anyhow!("type mismatch for argument {} in indirect call: expected {:?}, got {:?}", i+1, rpt, rat));
                            }
                        }
                        for a in args.iter().skip(params.len()) { let _ = self.type_expr(a)?; }
                        Ok(*ret)
                    };
                    match t_callee {
                        Type::Pointer(inner) => match *inner { Type::Func { ret, params, variadic } => return check_fn(ret, params, variadic), _ => {} },
                        Type::Func { ret, params, variadic } => return check_fn(ret, params, variadic),
                        _ => {}
                    }
                }

                if let Some((ret_t, params, variadic)) = self.func_sigs.get(callee).cloned() {
                    if !variadic && args.len() != params.len() { return Err(anyhow!("arity mismatch in call to {}: expected {}, got {}", callee, params.len(), args.len())); }
                    if variadic && args.len() < params.len() { return Err(anyhow!("too few arguments in call to {}: expected at least {}, got {}", callee, params.len(), args.len())); }
                    for (i, pty) in params.iter().enumerate() {
                        let pty_res = self.resolve_type(pty)?;
                        if matches!(pty_res, Type::Pointer(_)) && Sema::is_null_pointer_constant_expr(&args[i]) { continue; }
                        let aty = self.type_expr(&args[i])?;
                        if !self.type_compatible_for_param(pty, &aty)? {
                            let rpt = self.resolve_type(pty)?; let rat = self.resolve_type(&aty)?;
                            return Err(anyhow!("type mismatch for argument {} in call to {}: expected {:?}, got {:?}", i+1, callee, rpt, rat));
                        }
                    }
                    for a in args.iter().skip(params.len()) { let _ = self.type_expr(a)?; }
                    Ok(ret_t)
                } else {
                    for a in args { let _ = self.type_expr(a)?; }
                    Ok(Type::Int)
                }
            }

            Expr::CallPtr { target, args } => {
                let target_te = self.type_expr(target)?; let t_callee = self.resolve_type(&target_te)?;
                let mut check_fn = |ret: Box<Type>, params: Vec<Type>, variadic: bool| -> Result<Type> {
                    if !variadic && args.len() != params.len() { return Err(anyhow!("arity mismatch in indirect call: expected {}, got {}", params.len(), args.len())); }
                    if variadic && args.len() < params.len() { return Err(anyhow!("too few arguments in indirect call: expected at least {}, got {}", params.len(), args.len())); }
                    for (i, pty) in params.iter().enumerate() {
                        let pty_res = self.resolve_type(pty)?;
                        if matches!(pty_res, Type::Pointer(_)) && Sema::is_null_pointer_constant_expr(&args[i]) { continue; }
                        let aty = self.type_expr(&args[i])?;
                        if !self.type_compatible_for_param(pty, &aty)? {
                            let rpt = self.resolve_type(pty)?; let rat = self.resolve_type(&aty)?;
                            return Err(anyhow!("type mismatch for argument {} in indirect call: expected {:?}, got {:?}", i+1, rpt, rat));
                        }
                    }
                    for a in args.iter().skip(params.len()) { let _ = self.type_expr(a)?; }
                    Ok(*ret)
                };
                match t_callee {
                    Type::Pointer(inner) => match *inner { Type::Func { ret, params, variadic } => check_fn(ret, params, variadic), other => Err(anyhow!("call through non-function pointer: {:?}", other)) },
                    Type::Func { ret, params, variadic } => check_fn(ret, params, variadic),
                    other => Err(anyhow!("call through non-pointer expression: {:?}", other)),
                }
            }

            Expr::Cast { ty, expr } => { let _ = self.type_expr(expr)?; let r = self.resolve_type(ty)?; Ok(r) }

            Expr::SizeofType(ty) => { let r = self.resolve_type(ty)?; if !self.is_complete_object_type(&r) { return Err(anyhow!("sizeof of incomplete type")); } Ok(Type::Int) }
            Expr::SizeofExpr(e)  => { let te = self.type_expr(e)?; let t = self.resolve_type(&te)?; if !self.is_complete_object_type(&t) { return Err(anyhow!("sizeof of incomplete type")); } Ok(Type::Int) }

            Expr::IncDec { pre: _, inc: _, target } => { let _ = self.type_expr(target)?; Ok(Type::Int) }

            Expr::AssignOp { op: _, lhs, rhs } => {
                let _lt = self.type_expr(lhs)?; let _rt = self.type_expr(rhs)?;
                match &**lhs {
                    Expr::Ident(name) => self.lookup(name).ok_or_else(|| anyhow!("compound assign to undeclared identifier: {}", name)),
                    Expr::Unary { op: UnaryOp::Deref, expr } => { let ex = self.type_expr(expr)?; let pt = self.resolve_type(&ex)?; if let Type::Pointer(inner) = pt { Ok(*inner) } else { Err(anyhow!("compound assign to non-pointer deref")) } }
                    _ => Err(anyhow!("invalid compound assignment target")),
                }
            }
            Expr::Cond { cond, then_e, else_e } => {
                let _ = self.type_expr(cond)?; 
                let then_te = self.type_expr(then_e)?; let tt = self.resolve_type(&then_te)?;
                let else_te = self.type_expr(else_e)?; let et = self.resolve_type(&else_te)?;
                if let Some(t) = cond_result_type(&tt, &et) { return Ok(t); }
                if is_pointer(&tt) && is_pointer(&et) { return Ok(tt); }
                Ok(Type::Int)
            }

            Expr::Index { base, index } => {
                let base_te = self.type_expr(base)?; let bt = self.resolve_type(&base_te)?;
                let index_te = self.type_expr(index)?; let it = self.resolve_type(&index_te)?;
                if !is_integer(&it) { return Err(anyhow!("array subscript is not an integer")); }
                match bt { Type::Pointer(inner) => Ok(*inner), Type::Array(inner, _n) => Ok(*inner), other => Err(anyhow!("cannot index into non-pointer/array type: {:?}", other)) }
            }

            Expr::Member { base, field, arrow } => {
                let base_te = self.type_expr(base)?; let bt = self.resolve_type(&base_te)?;
                let (is_union, tag) = match (arrow, bt) {
                    (false, Type::Struct(t)) => (false, t),
                    (true, Type::Pointer(inner)) => match *inner { Type::Struct(t) => (false, t), Type::Union(t) => (true, t), other => { return Err(anyhow!("-> applied to non-pointer-to-struct/union: {:?}", other)); } },
                    (false, Type::Union(t)) => (true, t),
                    (false, other) => { return Err(anyhow!(". applied to non-struct/union type: {:?}", other)); }
                    (true, other)  => { return Err(anyhow!("-> applied to non-pointer type: {:?}", other)); }
                };
                if is_union {
                    if let Some(u) = self.union_layouts.get(&tag) { if let Some(ty) = u.members.get(field) { return Ok(ty.clone()); } return Err(anyhow!("unknown union field {} in union {}", field, tag)); }
                    else { return Ok(Type::Int); }
                } else {
                    if let Some(s) = self.struct_layouts.get(&tag) { if let Some((_off, ty)) = s.members.get(field) { return Ok(ty.clone()); } return Err(anyhow!("unknown struct field {} in struct {}", field, tag)); }
                    else { return Ok(Type::Int); }
                }
            }

            Expr::Comma { lhs, rhs } => { let _ = self.type_expr(lhs)?; let rt = self.type_expr(rhs)?; Ok(rt) }

            Expr::InitList(_items) => Err(anyhow!("initializer list cannot appear as an expression")),
        }
    }
}

/// Minimal semantic checker entry-point.
pub fn check_translation_unit(tu: &TranslationUnit) -> Result<()> {
    let mut sema = Sema::from_tu(tu);
    sema.check_tu(tu)?;
    check_labels_goto(tu)?;
    Ok(())
}

fn collect_labels_gotos(
    stmts: &[Stmt],
    labels: &mut HashSet<String>,
    gotos: &mut Vec<String>,
) -> Result<()> {
    for s in stmts {
        match s {
            Stmt::Block(inner) => collect_labels_gotos(inner, labels, gotos)?,
            Stmt::If { then_branch, else_branch, .. } => {
                collect_labels_gotos(then_branch, labels, gotos)?;
                if let Some(eb) = else_branch { collect_labels_gotos(eb, labels, gotos)?; }
            }
            Stmt::While { body, .. } => collect_labels_gotos(body, labels, gotos)?,
            Stmt::DoWhile { body, .. } => collect_labels_gotos(body, labels, gotos)?,
            Stmt::For { body, .. } => collect_labels_gotos(body, labels, gotos)?,
            Stmt::Switch { body, .. } => collect_labels_gotos(body, labels, gotos)?,
            Stmt::Case { .. } | Stmt::Default => { }
            Stmt::Label(name) => { if !labels.insert(name.clone()) { return Err(anyhow!("duplicate label: {}", name)); } }
            Stmt::Goto(name) => { gotos.push(name.clone()); }
            Stmt::Break | Stmt::Continue | Stmt::Return(_) | Stmt::Decl { .. } | Stmt::Typedef { .. } | Stmt::ExprStmt(_) => { }
        }
    }
    Ok(())
}

/// Verify per-function that all goto targets exist and labels are unique.
pub fn check_labels_goto(tu: &TranslationUnit) -> Result<()> {
    for f in &tu.functions {
        let mut labels: HashSet<String> = HashSet::new();
        let mut gotos: Vec<String> = Vec::new();
        collect_labels_gotos(&f.body, &mut labels, &mut gotos)?;
        for g in gotos { if !labels.contains(&g) { return Err(anyhow!("undefined label: {}", g)); } }
    }
    Ok(())
}

/// Placeholder for expression type inference (kept permissive).
pub fn infer_expr_type(_e: &Expr) -> Type { Type::Int }