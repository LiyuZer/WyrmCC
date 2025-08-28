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
        Type::Int => SIZEOF_INT,
        Type::Void => 0, // C89: sizeof(void) is invalid; sema should error later  keep 0 as a placeholder
        Type::Pointer(_) => SIZEOF_PTR,
        Type::Array(elem, n) => n.saturating_mul(sizeof_type(elem)),
        // New variants (placeholders for now); use record layouts via helpers for actual sizes
        Type::Enum(_) => SIZEOF_INT,
        Type::Struct(_) | Type::Union(_) => 0, // incomplete aggregates until full layout implemented
        Type::Named(_) => SIZEOF_INT, // typedef-name placeholder until resolved
    }
}

/// Return alignment (in bytes) of a type. Placeholder for now.
pub fn alignof_type(ty: &Type) -> usize {
    match ty {
        Type::Int => ALIGN_INT,
        Type::Void => 1, // arbitrary; void as an object type is invalid
        Type::Pointer(_) => ALIGN_PTR,
        Type::Array(elem, _n) => alignof_type(elem),
        // New variants (placeholders for now)
        Type::Enum(_) => ALIGN_INT,
        Type::Struct(_) | Type::Union(_) => ALIGN_INT,
        Type::Named(_) => ALIGN_INT,
    }
}

fn is_integer(ty: &Type) -> bool { matches!(ty, Type::Int) }
fn is_pointer(ty: &Type) -> bool { matches!(ty, Type::Pointer(_)) }

/// Try to perform a simple usual arithmetic conversion between two integer types
/// (for now we only have Int, so Int/Int -> Int).
fn usual_arith_conv(a: &Type, b: &Type) -> Option<Type> {
    if is_integer(a) && is_integer(b) { Some(Type::Int) } else { None }
}

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
    // Record layouts and enums for typing member access and sizeof in future
    struct_layouts: HashMap<String, StructLayout>,
    union_layouts: HashMap<String, UnionLayout>,
    enum_vals: HashMap<String, i64>,
    // New: global symbols (name -> type) for lookup within functions
    global_syms: HashMap<String, Type>,
}

impl Sema {
    fn new() -> Self { Self { scopes: Vec::new(), struct_layouts: HashMap::new(), union_layouts: HashMap::new(), enum_vals: HashMap::new(), global_syms: HashMap::new() } }

    fn from_tu(tu: &TranslationUnit) -> Self {
        let (s, u) = build_record_layouts(tu);
        let e = compute_enum_values(tu);
        Self { scopes: Vec::new(), struct_layouts: s, union_layouts: u, enum_vals: e, global_syms: HashMap::new() }
    }

    fn push_scope(&mut self) { self.scopes.push(HashMap::new()); }
    fn pop_scope(&mut self) { let _ = self.scopes.pop(); }

    fn insert(&mut self, name: String, ty: Type) { if let Some(s) = self.scopes.last_mut() { s.insert(name, ty); } }

    fn lookup(&self, name: &str) -> Option<Type> {
        for s in self.scopes.iter().rev() {
            if let Some(t) = s.get(name) { return Some(t.clone()); }
        }
        if let Some(t) = self.global_syms.get(name) { return Some(t.clone()); }
        None
    }

    fn process_globals(&mut self, tu: &TranslationUnit) -> Result<()> {
        let mut defined: HashSet<String> = HashSet::new();
        for g in &tu.globals {
            let name = g.name.clone();
            let ty = g.ty.clone();
            let is_extern = matches!(g.storage, Some(Storage::Extern));

            if !is_extern {
                // treat any non-extern declaration as a definition in this TU
                if !defined.insert(name.clone()) {
                    return Err(anyhow!("duplicate global definition: {}", name));
                }
            } else {
                // extern with initializer is not allowed
                if g.init.is_some() {
                    return Err(anyhow!("extern global '{}' cannot have initializer", name));
                }
            }

            if let Some(init) = &g.init {
                if !self.is_const_initializer(&ty, init) {
                    return Err(anyhow!("non-constant global initializer for {}", name));
                }
            }

            // Record in globals map for lookup in function bodies
            self.global_syms.entry(name).or_insert(ty);
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
        // Process globals first (collect types and validate initializers)
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
            self.insert(p.name.clone(), p.ty.clone());
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
            Stmt::Decl { name, ty, init } => {
                if let Some(e) = init { let _ = self.type_expr(e)?; }
                self.insert(name.clone(), ty.clone());
                Ok(())
            }
            Stmt::Typedef { name: _, ty: _ } => {
                // typedef has no runtime effect for now (namespaces to be added later)
                Ok(())
            }
            Stmt::ExprStmt(e) => { let _ = self.type_expr(e)?; Ok(()) }
        }
    }

    fn type_expr(&mut self, e: &Expr) -> Result<Type> {
        match e {
            Expr::Ident(name) => {
                self.lookup(name).ok_or_else(|| anyhow!("use of undeclared identifier: {}", name))
            }
            Expr::IntLiteral(_) => Ok(Type::Int),
            Expr::StringLiteral(_) => Ok(Type::Pointer(Box::new(Type::Int))), // char* approximated as int*

            Expr::Unary { op, expr } => {
                let t = self.type_expr(expr)?;
                match op {
                    UnaryOp::Plus | UnaryOp::Minus | UnaryOp::BitNot | UnaryOp::LogicalNot => {
                        if !is_integer(&t) { /* be permissive for now */ }
                        Ok(Type::Int)
                    }
                    UnaryOp::AddrOf => {
                        // Very permissive: & of an lvalue yields pointer to its type.
                        Ok(Type::Pointer(Box::new(t)))
                    }
                    UnaryOp::Deref => {
                        if let Type::Pointer(inner) = t { Ok(*inner) } else { Err(anyhow!("cannot dereference non-pointer")) }
                    }
                }
            }

            Expr::Binary { op, lhs, rhs } => {
                let lt = self.type_expr(lhs)?;
                let rt = self.type_expr(rhs)?;
                use BinaryOp as B;
                match op {
                    // arithmetic/bitwise/shift
                    B::Plus | B::Minus | B::Mul | B::Div | B::Mod |
                    B::Shl | B::Shr  | B::BitAnd | B::BitOr | B::BitXor => {
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
                    // logical && || -> int (truthiness)
                    B::LAnd | B::LOr => Ok(Type::Int),
                    // comparisons -> int; allow pointer eq/ne too (including pointer vs int null)
                    B::Lt | B::Le | B::Gt | B::Ge => {
                        if is_integer(&lt) && is_integer(&rt) { Ok(Type::Int) }
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
                let nt = self.lookup(name).ok_or_else(|| anyhow!("assignment to undeclared identifier: {}", name))?;
                // very permissive: allow int<-int and pointer<-pointer
                if (is_integer(&nt) && is_integer(&vt)) || (is_pointer(&nt) && is_pointer(&vt)) {
                    Ok(nt)
                } else {
                    Err(anyhow!("incompatible assignment to {}: {:?} = {:?}", name, nt, vt))
                }
            }

            Expr::AssignDeref { ptr, value } => {
                let pt = self.type_expr(ptr)?;
                let vt = self.type_expr(value)?;
                match pt {
                    Type::Pointer(inner) => {
                        // allow *ptr = int for now when inner is Int
                        if is_integer(&*inner) && is_integer(&vt) { Ok(*inner) } else { Ok(*inner) }
                    }
                    _ => Err(anyhow!("cannot assign through non-pointer"))
                }
            }

            Expr::Call { callee, args } => {
                // Minimal typing: assume functions return int
                if callee == "puts" {
                    // expect a pointer argument; be permissive
                    if !args.is_empty() { let _ = self.type_expr(&args[0])?; }
                    Ok(Type::Int)
                } else {
                    for a in args { let _ = self.type_expr(a)?; }
                    Ok(Type::Int)
                }
            }

            Expr::Cast { ty, expr } => {
                let _ = self.type_expr(expr)?; // ensure expr typeable; allow cast to any known type for now
                Ok(ty.clone())
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
                        if let Type::Pointer(inner) = pt { Ok(*inner) } else { Err(anyhow!("compound assign to non-pointer deref")) }
                    }
                    _ => Err(anyhow!("invalid compound assignment target"))
                }
            }
            Expr::Cond { cond, then_e, else_e } => {
                let _ct = self.type_expr(cond)?;
                let tt = self.type_expr(then_e)?;
                let et = self.type_expr(else_e)?;
                // simple unification: prefer int if both ints; pointer if both pointer (ignore base mismatch)
                if is_integer(&tt) && is_integer(&et) { Ok(Type::Int) }
                else if is_pointer(&tt) && is_pointer(&et) { Ok(tt) }
                else { Ok(Type::Int) }
            }

            Expr::Index { base, index } => {
                // a[i] where a is pointer-to-T or array-of-T and i is integer
                let bt = self.type_expr(base)?;
                let it = self.type_expr(index)?;
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
    sema.check_tu(tu)
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
}