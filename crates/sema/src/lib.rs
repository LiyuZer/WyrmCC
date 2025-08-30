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
        Type::Char | Type::SChar | Type::UChar
            | Type::Short | Type::UShort
            | Type::Int | Type::UInt
            | Type::Long | Type::ULong
            | Type::Enum(_)
    )
}

fn is_pointer(ty: &Type) -> bool { matches!(ty, Type::Pointer(_)) }

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
    matches!(ty, Type::Char | Type::SChar | Type::Short | Type::Int | Type::Long | Type::Enum(_))
}

fn integer_promotion(ty: &Type) -> Option<Type> {
    if !is_integer(ty) { return None; }
    // On this target, all narrow integer types promote to int
    if int_width(ty) < 32 { return Some(Type::Int); }
    Some(ty.clone())
}

/// Apply usual arithmetic conversions after integer promotions.
fn usual_arith_conv(a: &Type, b: &Type) -> Option<Type> {
    if !is_integer(a) || !is_integer(b) { return None; }
    let a = integer_promotion(a).unwrap();
    let b = integer_promotion(b).unwrap();
    if a == b { return Some(a); }
    use Type::*;

    // If either is unsigned long, result is unsigned long
    if matches!(a, ULong) || matches!(b, ULong) { return Some(ULong); }

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
pub fn promoted_int_type(t: &Type) -> Option<Type> { integer_promotion(t) }

/// Public: shift result is the promoted left operand type
pub fn shift_result_lhs_promoted(lhs: &Type) -> Option<Type> { integer_promotion(lhs) }

fn parse_int_literal_str(repr: &str) -> Option<i64> {
    if let Some(hex) = repr.strip_prefix("0x").or_else(|| repr.strip_prefix("0X")) {
        i64::from_str_radix(hex, 16).ok()
    } else if repr.len() > 1 && repr.starts_with('0') {
        // octal (fallback to decimal parse if empty after leading 0)
        i64::from_str_radix(&repr[1..], 8).ok().or_else(|| repr.parse::<i64>().ok())
    } else {
        repr.parse::<i64>().ok()
    }
}

fn eval_int_const_expr(e: &Expr) -> Option<i64> {
    match e {
        Expr::IntLiteral(s) => parse_int_literal_str(s),
        Expr::Unary { op: UnaryOp::Minus, expr } => eval_int_const_expr(expr).map(|v| -v),
        Expr::Unary { op: UnaryOp::Plus, expr } => eval_int_const_expr(expr),
        // Allow simple casts to int of a const int
        Expr::Cast { ty: Type::Int, expr } => eval_int_const_expr(expr),
        _ => None,
    }
}

fn round_up(x: usize, a: usize) -> usize { if a == 0 { x } else { (x + a - 1) / a * a } }

fn size_of_field(ty: &Type) -> usize { sizeof_type(ty) }
fn align_of_field(ty: &Type) -> usize { alignof_type(ty) }

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
    StructLayout { size, align: max_align.max(1), members: map }
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
    UnionLayout { size, align: max_align.max(1), members: map }
}

/// Build record layouts from a TranslationUnit's collected record definitions.
pub fn build_record_layouts(tu: &TranslationUnit) -> (HashMap<String, StructLayout>, HashMap<String, UnionLayout>) {
    let mut structs: HashMap<String, StructLayout> = HashMap::new();
    let mut unions: HashMap<String, UnionLayout> = HashMap::new();
    for r in &tu.records {
        match r.kind {
            RecordKind::Struct => { structs.insert(r.tag.clone(), build_struct_layout(&r.members)); }
            RecordKind::Union => { unions.insert(r.tag.clone(), build_union_layout(&r.members)); }
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
    fn new() -> Self { Self { scopes: Vec::new(), typedef_scopes: Vec::new(), struct_layouts: HashMap::new(), union_layouts: HashMap::new(), enum_vals: HashMap::new(), global_syms: HashMap::new(), func_sigs: HashMap::new() } }

    fn from_tu(tu: &TranslationUnit) -> Self {
        let (s, u) = build_record_layouts(tu);
        let e = compute_enum_values(tu);
        let mut me = Self { scopes: Vec::new(), typedef_scopes: Vec::new(), struct_layouts: s, union_layouts: u, enum_vals: e, global_syms: HashMap::new(), func_sigs: HashMap::new() };
        me.populate_function_signatures(tu);
        me
    }

    fn populate_function_signatures(&mut self, tu: &TranslationUnit) {
        // Collect from TU definitions
        for f in &tu.functions {
            let params: Vec<Type> = f.params.iter().map(|p| p.ty.clone()).collect();
            self.func_sigs.insert(f.name.clone(), (f.ret_type.clone(), params, f.variadic));
        }
        // Built-ins used by tests/runtime
        // puts: int puts(char*) -> approximate as int*(ptr to int)
        self.func_sigs.entry("puts".to_string()).or_insert((Type::Int, vec![Type::Pointer(Box::new(Type::Int))], false));
        // printf: int printf(char*, ...) -> approximate as int*(ptr to int), variadic
        self.func_sigs.entry("printf".to_string()).or_insert((Type::Int, vec![Type::Pointer(Box::new(Type::Int))], true));
    }

    fn push_scope(&mut self) { self.scopes.push(HashMap::new()); self.typedef_scopes.push(HashMap::new()); }
    fn pop_scope(&mut self) { let _ = self.scopes.pop(); let _ = self.typedef_scopes.pop(); }

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
                if !seen.insert(nm.clone()) {
                    return Err(anyhow!("cyclic typedef detected: {}", nm));
                }
                let base = self.lookup_typedef(nm).ok_or_else(|| anyhow!("unknown typedef name: {}", nm))?;
                let out = self.resolve_type_internal(&base, seen)?;
                Ok(out)
            }
            Type::Pointer(inner) => {
                let r = self.resolve_type_internal(inner, seen)?;
                Ok(Type::Pointer(Box::new(r)))
            }
            Type::Array(inner, n) => {
                let r = self.resolve_type_internal(inner, seen)?;
                Ok(Type::Array(Box::new(r), *n))
            }
            other => Ok(other.clone()),
        }
    }

    fn resolve_type(&self, ty: &Type) -> Result<Type> {
        let mut seen: HashSet<String> = HashSet::new();
        self.resolve_type_internal(ty, &mut seen)
    }

    fn process_globals(&mut self, tu: &TranslationUnit) -> Result<()> {
        // First pass: collect per-name info across the TU
        #[derive(Default)]
        struct Info { has_extern: bool, defs: usize, tentatives: usize }
        let mut map: HashMap<String, Info> = HashMap::new();

        for g in &tu.globals {
            let name = g.name.clone();
            let ty = g.ty.clone();
            let is_extern = matches!(g.storage, Some(Storage::Extern));
            let has_init = g.init.is_some();

            // extern with initializer is invalid
            if is_extern && has_init {
                return Err(anyhow!("extern global '{}' cannot have initializer", name));
            }

            // Validate constant initializer when present
            if let Some(init) = &g.init {
                if !self.is_const_initializer(&ty, init) {
                    return Err(anyhow!("non-constant global initializer for {}", name));
                }
            }

            // Aggregate counts
            let entry = map.entry(name.clone()).or_default();
            if is_extern {
                entry.has_extern = true;
            } else if has_init {
                entry.defs = entry.defs.saturating_add(1);
            } else {
                // non-extern without init: tentative definition
                entry.tentatives = entry.tentatives.saturating_add(1);
            }

            // Record in globals map for lookup in function bodies (first-seen wins)
            self.global_syms.entry(name).or_insert(ty);
        }

        // Diagnostics: more than one actual definition within the same TU is an error
        for (name, info) in &map {
            if info.defs > 1 {
                return Err(anyhow!("duplicate global definition: {}", name));
            }
        }

        Ok(())
    }

    fn is_const_initializer(&self, ty: &Type, e: &Expr) -> bool {
        match ty {
            Type::Int => eval_int_const_expr(e).is_some(),
            Type::Pointer(inner) => {
                match e {
                    // Direct string literal -> OK for pointer-to-int
                    Expr::StringLiteral(_) => matches!(&**inner, Type::Int),
                    // Cast to pointer from string literal or integer 0
                    Expr::Cast { ty: Type::Pointer(_), expr } => {
                        match expr.as_ref() {
                            Expr::StringLiteral(_) => matches!(&**inner, Type::Int),
                            Expr::IntLiteral(s) => parse_int_literal_str(s).map_or(false, |v| v == 0),
                            _ => false,
                        }
                    }
                    // Allow plain 0 as null initializer
                    Expr::IntLiteral(s) => parse_int_literal_str(s).map_or(false, |v| v == 0),
                    _ => false,
                }
            }
            Type::Array(_elem, _n) => {
                // Brace initializers not yet supported; accept only zero-init via explicit 0 (optional) or none
                match e {
                    Expr::IntLiteral(s) => parse_int_literal_str(s).map_or(false, |v| v == 0),
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn check_tu(&mut self, tu: &TranslationUnit) -> Result<()> {
        // Gather function signatures (already done in from_tu) and process globals
        self.process_globals(tu)?;
        for f in &tu.functions {
            self.check_function(f)?;
        }
        Ok(())
    }

    fn check_function(&mut self, f: &Function) -> Result<()> {
        // Start a fresh scope for params
        self.push_scope();
        for p in &f.params {
            let rty = self.resolve_type(&p.ty)?;
            self.insert(p.name.clone(), rty);
        }
        // Function body
        self.check_block(&f.body)?;
        self.pop_scope();
        Ok(())
    }

    fn check_block(&mut self, body: &[Stmt]) -> Result<()> {
        self.push_scope();
        for s in body {
            self.check_stmt(s)?;
        }
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
                    if !seen_cases.insert(v) {
                        return Err(anyhow!("duplicate case label: {}", v));
                    }
                }
                Stmt::Default => {
                    if seen_default { return Err(anyhow!("multiple default labels in switch")); }
                    seen_default = true;
                }
                other => {
                    // Regular statement inside switch
                    self.check_stmt(other)?;
                }
            }
        }
        Ok(())
    }

    fn check_stmt(&mut self, s: &Stmt) -> Result<()> {
        match s {
            Stmt::Block(stmts) => self.check_block(stmts),
            Stmt::If { cond, then_branch, else_branch } => {
                let _ = self.type_expr(cond)?; // ensure cond is typeable
                self.check_block(then_branch)?;
                if let Some(eb) = else_branch { self.check_block(eb)?; }
                Ok(())
            }
            Stmt::While { cond, body } => {
                let _ = self.type_expr(cond)?;
                self.check_block(body)
            }
            Stmt::DoWhile { body, cond } => {
                let _ = self.type_expr(cond)?;
                self.check_block(body)
            }
            Stmt::For { init, cond, post, body } => {
                if let Some(i) = init { let _ = self.type_expr(i)?; }
                if let Some(c) = cond { let _ = self.type_expr(c)?; }
                if let Some(p) = post { let _ = self.type_expr(p)?; }
                self.check_block(body)
            }
            Stmt::Switch { cond, body } => {
                let ct = self.type_expr(cond)?;
                if !is_integer(&ct) { return Err(anyhow!("switch condition is not integer")); }
                self.check_switch_body(body)
            }
            Stmt::Case { .. } => {
                // Labels are validated within the enclosing Switch; accept here.
                Ok(())
            }
            Stmt::Default => {
                // Validated within the enclosing Switch; accept here.
                Ok(())
            }
            Stmt::Break | Stmt::Continue => Ok(()),
            Stmt::Return(e) => { let _ = self.type_expr(e)?; Ok(()) }
            Stmt::Decl { name, ty, init, .. } => {
                let rty = self.resolve_type(ty)?;
                if let Some(e) = init { let _ = self.type_expr(e)?; }
                self.insert(name.clone(), rty);
                Ok(())
            }
            Stmt::Typedef { name, ty } => {
                let rty = self.resolve_type(ty)?;
                if let Some(scope) = self.typedef_scopes.last_mut() {
                    if scope.contains_key(name) {
                        return Err(anyhow!("redefinition of typedef {} in the same scope", name));
                    }
                    scope.insert(name.clone(), rty);
                    Ok(())
                } else {
                    Err(anyhow!("typedef outside of any scope"))
                }
            }
            Stmt::Label(_name) => { Ok(()) }
            Stmt::Goto(_name) => { Ok(()) }
            Stmt::ExprStmt(e) => { let _ = self.type_expr(e)?; Ok(()) }
        }
    }

    fn decay_array_to_ptr(&self, t: &Type) -> Result<Type> {
        let r = self.resolve_type(t)?;
        match r {
            Type::Array(inner, _n) => Ok(Type::Pointer(inner)),
            other => Ok(other),
        }
    }

    fn type_compatible_for_param(&self, param: &Type, arg: &Type) -> Result<bool> {
        let p = self.resolve_type(param)?;
        let a = self.decay_array_to_ptr(arg)?;
        Ok((is_integer(&p) && is_integer(&a)) || (is_pointer(&p) && is_pointer(&a)))
    }

    fn type_expr(&mut self, e: &Expr) -> Result<Type> {
        match e {
            Expr::Ident(name) => {
                if let Some(t) = self.lookup(name) { return Ok(t); }
                if let Some((ret, params, variadic)) = self.func_sigs.get(name).cloned() {
                    // Function designator: treat identifier as a function type
                    return Ok(Type::Func { ret: Box::new(ret), params, variadic });
                }
                Err(anyhow!("use of undeclared identifier: {}", name))
            }
            Expr::IntLiteral(_) => Ok(Type::Int),
            Expr::StringLiteral(_) => Ok(Type::Pointer(Box::new(Type::Int))), // char*

            Expr::Unary { op, expr } => {
                let t = self.type_expr(expr)?;
                match op {
                    UnaryOp::Plus | UnaryOp::Minus | UnaryOp::BitNot | UnaryOp::LogicalNot => {
                        if !is_integer(&self.resolve_type(&t)?) { /* be permissive for now */ }
                        Ok(Type::Int)
                    }
                    UnaryOp::AddrOf => {
                        let rt = self.resolve_type(&t)?;
                        Ok(Type::Pointer(Box::new(rt)))
                    }
                    UnaryOp::Deref => {
                        let rt = self.resolve_type(&t)?;
                        if let Type::Pointer(inner) = rt { Ok(*inner) } else { Err(anyhow!("cannot dereference non-pointer")) }
                    }
                }
            }

            Expr::Binary { op, lhs, rhs } => {
                let lt_raw = self.type_expr(lhs)?;
                let rt_raw = self.type_expr(rhs)?;
                let lt_res = self.resolve_type(&lt_raw)?;
                let rt_res = self.resolve_type(&rt_raw)?;
                // Decay array types to pointers where applicable
                let lt = match lt_res { Type::Array(inner, _) => Type::Pointer(inner), other => other };
                let rt = match rt_res { Type::Array(inner, _) => Type::Pointer(inner), other => other };
                use BinaryOp as B;
                match op {
                    // arithmetic and bitwise (excluding shifts)
                    B::Plus | B::Minus | B::Mul | B::Div | B::Mod | B::BitAnd | B::BitOr | B::BitXor => {
                        // pointer arithmetic cases for +/-
                        if matches!(op, B::Plus | B::Minus) {
                            match (&lt, &rt) {
                                (Type::Pointer(_), Type::Int) => return Ok(lt),
                                (Type::Int, Type::Pointer(_)) if matches!(op, B::Plus) => return Ok(rt),
                                (Type::Pointer(_), Type::Pointer(_)) if matches!(op, B::Minus) => return Ok(Type::Int),
                                _ => {}
                            }
                        }
                        usual_arith_conv(&lt, &rt).ok_or_else(|| anyhow!("invalid arithmetic between {:?} and {:?}", lt, rt))
                    }
                    // shifts: result is the promoted left operand type; rhs is converted to int
                    B::Shl | B::Shr => {
                        if !is_integer(&lt) || !is_integer(&rt) {
                            return Err(anyhow!("invalid shift between {:?} and {:?}", lt, rt));
                        }
                        promoted_int_type(&lt).ok_or_else(|| anyhow!("failed to promote shift lhs"))
                    }
                    // logical && || -> int (truthiness)
                    B::LAnd | B::LOr => Ok(Type::Int),
                    // comparisons -> int; require arithmetic types (apply UAC for validation)
                    B::Lt | B::Le | B::Gt | B::Ge => {
                        if usual_arith_conv(&lt, &rt).is_some() { Ok(Type::Int) }
                        else { Err(anyhow!("invalid relational compare between {:?} and {:?}", lt, rt)) }
                    }
                    B::Eq | B::Ne => {
                        if (is_integer(&lt) && is_integer(&rt))
                            || (is_pointer(&lt) && is_pointer(&rt))
                            || (is_pointer(&lt) && is_integer(&rt))
                            || (is_integer(&lt) && is_pointer(&rt))
                        { Ok(Type::Int) } else {
                            Err(anyhow!("invalid equality compare between {:?} and {:?}", lt, rt))
                        }
                    }
                }
            }

            Expr::Assign { name, value } => {
                let vt = self.type_expr(value)?;
                let vt = self.resolve_type(&vt)?;
                let nt = self.lookup(name).ok_or_else(|| anyhow!("assignment to undeclared identifier: {}", name))?;
                let nt = self.resolve_type(&nt)?;
                // very permissive: allow int<-int and pointer<-pointer
                if (is_integer(&nt) && is_integer(&vt)) || (is_pointer(&nt) && is_pointer(&vt)) {
                    Ok(nt)
                } else {
                    Err(anyhow!("incompatible assignment to {}: {:?} = {:?}", name, nt, vt))
                }
            }

            Expr::AssignDeref { ptr, value } => {
                let pt = self.type_expr(ptr)?;
                let pt = self.resolve_type(&pt)?;
                let vt = self.type_expr(value)?;
                let vt = self.resolve_type(&vt)?;
                match pt {
                    Type::Pointer(inner) => {
                        // allow *ptr = int for now when inner is Int
                        if is_integer(&*inner) && is_integer(&vt) { Ok(*inner) } else { Ok(*inner) }
                    }
                    _ => Err(anyhow!("cannot assign through non-pointer"))
                }
            }

            Expr::Call { callee, args } => {
                // If callee is a variable in scope with a function pointer/function type,
                // treat this as an indirect call and perform full arity/type checks.
                if let Some(vt) = self.lookup(callee) {
                    let t_callee = self.resolve_type(&vt)?;
                    let mut check_fn = |ret: Box<Type>, params: Vec<Type>, variadic: bool| -> Result<Type> {
                        if !variadic && args.len() != params.len() {
                            return Err(anyhow!(
                                "arity mismatch in indirect call: expected {}, got {}",
                                params.len(), args.len()
                            ));
                        }
                        if variadic && args.len() < params.len() {
                            return Err(anyhow!(
                                "too few arguments in indirect call: expected at least {}, got {}",
                                params.len(), args.len()
                            ));
                        }
                        for (i, pty) in params.iter().enumerate() {
                            let aty = self.type_expr(&args[i])?;
                            if !self.type_compatible_for_param(pty, &aty)? {
                                let rpt = self.resolve_type(pty)?;
                                let rat = self.resolve_type(&aty)?;
                                return Err(anyhow!(
                                    "type mismatch for argument {} in indirect call: expected {:?}, got {:?}",
                                    i+1, rpt, rat
                                ));
                            }
                        }
                        for a in args.iter().skip(params.len()) { let _ = self.type_expr(a)?; }
                        Ok(*ret)
                    };
                    match t_callee {
                        Type::Pointer(inner) => match *inner {
                            Type::Func { ret, params, variadic } => return check_fn(ret, params, variadic),
                            _ => {}
                        },
                        Type::Func { ret, params, variadic } => return check_fn(ret, params, variadic),
                        _ => {}
                    }
                }

                if let Some((ret_t, params, variadic)) = self.func_sigs.get(callee).cloned() {
                    // Arity checks for known function symbols
                    if !variadic && args.len() != params.len() {
                        return Err(anyhow!(
                            "arity mismatch in call to {}: expected {}, got {}",
                            callee, params.len(), args.len()
                        ));
                    }
                    if variadic && args.len() < params.len() {
                        return Err(anyhow!(
                            "too few arguments in call to {}: expected at least {}, got {}",
                            callee, params.len(), args.len()
                        ));
                    }
                    // Check fixed arguments
                    for (i, pty) in params.iter().enumerate() {
                        let aty = self.type_expr(&args[i])?;
                        if !self.type_compatible_for_param(pty, &aty)? {
                            let rpt = self.resolve_type(pty)?;
                            let rat = self.resolve_type(&aty)?;
                            return Err(anyhow!(
                                "type mismatch for argument {} in call to {}: expected {:?}, got {:?}",
                                i+1, callee, rpt, rat
                            ));
                        }
                    }
                    // Check the rest (variadic part) are typeable
                    for a in args.iter().skip(params.len()) {
                        let _ = self.type_expr(a)?; // ensure typeable
                    }
                    Ok(ret_t)
                } else {
                    // Unknown extern: be permissive, type-check args only
                    for a in args { let _ = self.type_expr(a)?; }
                    Ok(Type::Int)
                }
            }

            Expr::CallPtr { target, args } => {
                // Indirect call via function pointer or function designator
                let t_callee = self.type_expr(target)?;
                let t_callee = self.resolve_type(&t_callee)?;
                // Helper to check args against a function type and return its ret type
                let mut check_fn = |ret: Box<Type>, params: Vec<Type>, variadic: bool| -> Result<Type> {
                    if !variadic && args.len() != params.len() {
                        return Err(anyhow!(
                            "arity mismatch in indirect call: expected {}, got {}",
                            params.len(), args.len()
                        ));
                    }
                    if variadic && args.len() < params.len() {
                        return Err(anyhow!(
                            "too few arguments in indirect call: expected at least {}, got {}",
                            params.len(), args.len()
                        ));
                    }
                    for (i, pty) in params.iter().enumerate() {
                        let aty = self.type_expr(&args[i])?;
                        if !self.type_compatible_for_param(pty, &aty)? {
                            let rpt = self.resolve_type(pty)?;
                            let rat = self.resolve_type(&aty)?;
                            return Err(anyhow!(
                                "type mismatch for argument {} in indirect call: expected {:?}, got {:?}",
                                i+1, rpt, rat
                            ));
                        }
                    }
                    for a in args.iter().skip(params.len()) { let _ = self.type_expr(a)?; }
                    Ok(*ret)
                };

                match t_callee {
                    Type::Pointer(inner) => match *inner {
                        Type::Func { ret, params, variadic } => check_fn(ret, params, variadic),
                        other => Err(anyhow!("call through non-function pointer: {:?}", other)),
                    },
                    Type::Func { ret, params, variadic } => check_fn(ret, params, variadic),
                    other => Err(anyhow!("call through non-pointer expression: {:?}", other)),
                }
            }

            Expr::Cast { ty, expr } => {
                let _ = self.type_expr(expr)?; // ensure expr typeable; allow cast to any known type for now
                let r = self.resolve_type(ty)?;
                Ok(r)
            }
            Expr::SizeofType(_ty) => Ok(Type::Int),
            Expr::SizeofExpr(e) => { let _ = self.type_expr(e)?; Ok(Type::Int) }

            Expr::IncDec { pre: _, inc: _, target } => {
                // ++/-- valid on int lvalues or *ptr; result type int for now
                let _ = self.type_expr(target)?;
                Ok(Type::Int)
            }
            Expr::AssignOp { op: _, lhs, rhs } => {
                let _lt = self.type_expr(lhs)?;
                let _rt = self.type_expr(rhs)?;
                // Accept for now and return lhs type
                match &**lhs {
                    Expr::Ident(name) => self.lookup(name).ok_or_else(|| anyhow!("compound assign to undeclared identifier: {}", name)),
                    Expr::Unary { op: UnaryOp::Deref, expr } => {
                        let pt = self.type_expr(expr)?;
                        let pt = self.resolve_type(&pt)?;
                        if let Type::Pointer(inner) = pt { Ok(*inner) } else { Err(anyhow!("compound assign to non-pointer deref")) }
                    }
                    _ => Err(anyhow!("invalid compound assignment target"))
                }
            }
            Expr::Cond { cond, then_e, else_e } => {
                let _ct = self.type_expr(cond)?;
                let tt = self.type_expr(then_e)?;
                let et = self.type_expr(else_e)?;
                let tt = self.resolve_type(&tt)?;
                let et = self.resolve_type(&et)?;
                if let Some(t) = cond_result_type(&tt, &et) { return Ok(t); }
                if is_pointer(&tt) && is_pointer(&et) { return Ok(tt); }
                Ok(Type::Int)
            }

            Expr::Index { base, index } => {
                // a[i] where a is pointer-to-T or array-of-T and i is integer
                let bt = self.type_expr(base)?;
                let bt = self.resolve_type(&bt)?;
                let it = self.type_expr(index)?;
                let it = self.resolve_type(&it)?;
                if !is_integer(&it) {
                    return Err(anyhow!("array subscript is not an integer"));
                }
                match bt {
                    Type::Pointer(inner) => Ok(*inner),
                    Type::Array(inner, _n) => Ok(*inner),
                    other => Err(anyhow!("cannot index into non-pointer/array type: {:?}", other)),
                }
            }

            // Member access: resolve via record layouts if available
            Expr::Member { base, field, arrow } => {
                let bt = self.type_expr(base)?;
                let bt = self.resolve_type(&bt)?;
                // Determine record kind and tag
                let (is_union, tag) = match (arrow, bt) {
                    (false, Type::Struct(t)) => (false, t),
                    (true, Type::Pointer(inner)) => match *inner {
                        Type::Struct(t) => (false, t),
                        Type::Union(t) => (true, t),
                        other => return Err(anyhow!("-> applied to non-pointer-to-struct/union: {:?}", other)),
                    },
                    (false, Type::Union(t)) => (true, t),
                    (false, other) => return Err(anyhow!(". applied to non-struct/union type: {:?}", other)),
                    (true, other) => return Err(anyhow!("-> applied to non-pointer type: {:?}", other)),
                };
                if is_union {
                    if let Some(u) = self.union_layouts.get(&tag) {
                        if let Some(ty) = u.members.get(field) { return Ok(ty.clone()); }
                        return Err(anyhow!("unknown union field {} in union {}", field, tag));
                    } else {
                        // incomplete union
                        return Ok(Type::Int);
                    }
                } else {
                    if let Some(s) = self.struct_layouts.get(&tag) {
                        if let Some((_off, ty)) = s.members.get(field) { return Ok(ty.clone()); }
                        return Err(anyhow!("unknown struct field {} in struct {}", field, tag));
                    } else {
                        // incomplete struct
                        return Ok(Type::Int);
                    }
                }
            }

            // Comma operator: type is RHS; both sides must be typeable
            Expr::Comma { lhs, rhs } => {
                let _ = self.type_expr(lhs)?;
                let rt = self.type_expr(rhs)?;
                Ok(rt)
            }
        }
    }
}

/// Minimal semantic checker entry-point.
/// Currently permissive and aims not to reject code used by existing tests.
pub fn check_translation_unit(tu: &TranslationUnit) -> Result<()> {
    let mut sema = Sema::from_tu(tu);
    sema.check_tu(tu)?;
    // Additional pass: labels/goto validation
    check_labels_goto(tu)?;
    Ok(())
}

/// Collect labels and gotos within a list of statements.
fn collect_labels_gotos(stmts: &[Stmt], labels: &mut HashSet<String>, gotos: &mut Vec<String>) -> Result<()> {
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
            Stmt::Case { .. } | Stmt::Default => { /* switch labels handled in another pass */ }
            Stmt::Label(name) => {
                if !labels.insert(name.clone()) {
                    return Err(anyhow!("duplicate label: {}", name));
                }
            }
            Stmt::Goto(name) => { gotos.push(name.clone()); }
            Stmt::Break | Stmt::Continue | Stmt::Return(_) | Stmt::Decl { .. } | Stmt::Typedef { .. } | Stmt::ExprStmt(_) => { /* no-op */ }
        }
    }
    Ok(())
}

/// Public: verify per-function that all goto targets exist and labels are unique.
pub fn check_labels_goto(tu: &TranslationUnit) -> Result<()> {
    for f in &tu.functions {
        let mut labels: HashSet<String> = HashSet::new();
        let mut gotos: Vec<String> = Vec::new();
        collect_labels_gotos(&f.body, &mut labels, &mut gotos)?;
        for g in gotos {
            if !labels.contains(&g) {
                return Err(anyhow!("undefined label: {}", g));
            }
        }
    }
    Ok(())
}

/// Placeholder for expression type inference (will use symbol tables in future).
/// For now, only recognize some literals and very basic forms; fall back to Int.
pub fn infer_expr_type(_e: &Expr) -> Type {
    // Without symbol/type environment, default to int.
    Type::Int
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizeof_int_is_4() {
        assert_eq!(sizeof_type(&Type::Int), 4);
    }

    #[test]
    fn sizeof_ptr_is_8() {
        assert_eq!(sizeof_type(&Type::Pointer(Box::new(Type::Int))), 8);
    }

    #[test]
    fn align_basic_types() {
        assert_eq!(alignof_type(&Type::Int), 4);
        assert_eq!(alignof_type(&Type::Pointer(Box::new(Type::Int))), 8);
        assert_eq!(alignof_type(&Type::Array(Box::new(Type::Int), 10)), 4);
    }

    #[test]
    fn check_tu_noop_ok() {
        let src = r#"
            int main(void) { return 0; }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        check_translation_unit(&tu).expect("sema ok");
    }

    #[test]
    fn sema_handles_addr_and_deref() {
        let src = r#"
            int main(void) {
                int x; int *p; p = &x; x = 7; *p = 3; return x;
            }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        check_translation_unit(&tu).expect("sema ok");
    }

    #[test]
    fn sema_permits_pointer_addition() {
        let src = r#"
            int main(void) {
                int x; int *p; p = &x; p = p + 1; return 0;
            }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        check_translation_unit(&tu).expect("sema ok");
    }

    #[test]
    fn sema_struct_layout_offsets() {
        let src = r#"
            int main(void) {
                struct S { int a; int b; } s;
                return 0;
            }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        let (smap, _umap) = build_record_layouts(&tu);
        let s = smap.get("").or_else(|| smap.get("S")).expect("struct layout present");
        // Offsets and sizes for two ints
        let (off_a, ty_a) = s.members.get("a").expect("field a");
        let (off_b, ty_b) = s.members.get("b").expect("field b");
        assert_eq!(*off_a, 0);
        assert_eq!(*off_b, 4);
        assert!(matches!(ty_a, Type::Int));
        assert!(matches!(ty_b, Type::Int));
        assert_eq!(s.size, 8);
        assert_eq!(s.align, 4);
    }

    #[test]
    fn sema_union_layout() {
        let src = r#"
            int main(void) {
                union U { int a; int *p; } u;
                return 0;
            }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        let (_smap, umap) = build_record_layouts(&tu);
        let u = umap.get("").or_else(|| umap.get("U")).expect("union layout present");
        assert_eq!(u.size, 8);
        assert_eq!(u.align, 8);
        assert!(matches!(u.members.get("a").cloned().unwrap(), Type::Int));
        assert!(matches!(u.members.get("p").cloned().unwrap(), Type::Pointer(_)));
    }

    #[test]
    fn sema_member_access_types_and_checks() {
        let src = r#"
            int main(void) {
                struct S { int a; int *p; } s;
                struct S *q = &s;
                s.a = 1;
                q->a = 2;
                return 0;
            }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        // If member typing is broken (unknown fields or wrong base), this will error
        check_translation_unit(&tu).expect("member access type-checks");
    }

    #[test]
    fn sema_enum_values() {
        let src = r#"
            int main(void) {
                enum E { A=1, B, C=5 } e;
                return 0;
            }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        let m = compute_enum_values(&tu);
        assert_eq!(m.get("A").copied(), Some(1));
        assert_eq!(m.get("B").copied(), Some(2));
        assert_eq!(m.get("C").copied(), Some(5));
    }

    // ===== Labels/Goto tests =====
    #[test]
    fn labels_goto_forward_ok() {
        let src = r#"
            int main(void){ goto L; L: return 0; }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        check_translation_unit(&tu).expect("labels/goto forward ok");
    }

    #[test]
    fn labels_goto_backward_ok() {
        let src = r#"
            int main(void){ L: return 1; goto L; }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        check_translation_unit(&tu).expect("labels/goto backward ok");
    }

    #[test]
    fn labels_goto_undefined_err() {
        let src = r#"
            int main(void){ goto M; L: return 0; }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        let err = check_translation_unit(&tu).expect_err("should error on undefined label");
        assert!(format!("{}", err).contains("undefined label: M"));
    }

    #[test]
    fn labels_goto_duplicate_err() {
        let src = r#"
            int main(void){ L: return 0; L: return 1; }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        let err = check_translation_unit(&tu).expect_err("should error on duplicate label");
        assert!(format!("{}", err).contains("duplicate label: L"));
    }

    #[test]
    fn labels_goto_nested_block_ok() {
        let src = r#"
            int f(void){ { L: ; } goto L; return 0; }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        check_translation_unit(&tu).expect("function-scoped labels ok");
    }

    // ===== Function prototype and call checking tests =====
    #[test]
    fn call_arity_too_few_args_errors() {
        let src = r#"
            int f(int a, int b) { return 0; }
            int main(void) { return f(1); }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        let err = check_translation_unit(&tu).expect_err("should error on too few args");
        let s = err.to_string();
        assert!(s.contains("too few") || s.contains("arity"));
    }

    #[test]
    fn call_arity_too_many_args_errors() {
        let src = r#"
            int f(int a) { return 0; }
            int main(void) { return f(1, 2); }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        let err = check_translation_unit(&tu).expect_err("should error on too many args");
        let s = err.to_string();
        assert!(s.contains("arity") || s.contains("too"));
    }

    #[test]
    fn call_type_mismatch_in_fixed_param_errors() {
        let src = r#"
            int f(int a, int b) { return a + b; }
            int main(void) { int x; int *p = &x; return f(p, 2); }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        let err = check_translation_unit(&tu).expect_err("should error on type mismatch");
        assert!(format!("{}", err).contains("type mismatch"));
    }

    #[test]
    fn variadic_allows_extra_arguments() {
        let src = r#"
            int v(int a, ...) { return a; }
            int main(void) { return v(1, 2, 3); }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        check_translation_unit(&tu).expect("variadic extra ok");
    }

    #[test]
    fn variadic_fixed_part_type_mismatch_errors() {
        let src = r#"
            int v(int a, ...) { return a; }
            int main(void) { int *p = 0; return v(p, 2); }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        let err = check_translation_unit(&tu).expect_err("should error on fixed arg type mismatch");
        assert!(format!("{}", err).contains("type mismatch"));
    }

    #[test]
    fn builtin_printf_requires_pointer_first_param() {
        let src = r#"
            int main(void) { return printf(1); }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        let err = check_translation_unit(&tu).expect_err("printf first arg must be pointer");
        let s = err.to_string();
        assert!(s.contains("type mismatch") || s.contains("expected Pointer"));
    }

    #[test]
    fn builtin_puts_accepts_string_literal() {
        let src = r#"
            int main(void) { return puts("hi"); }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        check_translation_unit(&tu).expect("puts ok");
    }

    // ===== Typedef resolution tests =====
    #[test]
    fn typedef_basic_alias() {
        let src = r#"
            int main(void) {
                typedef int I; I x; x = 3; return x;
            }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        check_translation_unit(&tu).expect("typedef basic alias ok");
    }

    #[test]
    fn typedef_pointer_alias_and_arith() {
        let src = r#"
            int main(void) {
                int x; typedef int* P; P p = &x; p = p + 1; return 0;
            }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        check_translation_unit(&tu).expect("typedef pointer alias ok");
    }

    #[test]
    fn typedef_struct_alias_and_member() {
        let src = r#"
            int main(void) {
                typedef struct S { int a; } S; S s; s.a = 1; return 0;
            }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        check_translation_unit(&tu).expect("typedef struct alias ok");
    }

    #[test]
    fn typedef_array_alias_and_index() {
        let src = r#"
            int main(void) {
                typedef int A[10]; A a; a[1] = 2; return 0;
            }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        check_translation_unit(&tu).expect("typedef array alias ok");
    }

    #[test]
    fn typedef_shadowing_allows_inner_redefinition() {
        let src = r#"
            int main(void) {
                typedef int I; { typedef unsigned int I; I y; } I x; return 0;
            }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        check_translation_unit(&tu).expect("typedef shadowing ok");
    }

    #[test]
    fn typedef_same_scope_redefinition_errors() {
        let src = r#"
            int main(void) {
                typedef int I; typedef int I; return 0;
            }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        let err = check_translation_unit(&tu).expect_err("redefinition in same scope should error");
        assert!(format!("{}", err).contains("redefinition of typedef I"));
    }

    #[test]
    fn unknown_typedef_name_in_decl_errors() {
        let src = r#"
            int main(void) { T x; return 0; }
        "#;
        let tu = parse::parse_translation_unit(src).expect("parse ok");
        let err = check_translation_unit(&tu).expect_err("unknown typedef in decl should error");
        let s = err.to_string();
        assert!(s.contains("unknown typedef name") || s.contains("unknown"));
    }
}