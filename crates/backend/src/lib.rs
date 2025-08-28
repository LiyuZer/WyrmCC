use anyhow::Result;
use parse::ast::{BinaryOp, Expr, Function as AstFn, RecordKind, Stmt, TranslationUnit, Type, UnaryOp};
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

pub fn emit_llvm_ir(tu: &TranslationUnit, module_name: &str) -> Result<String> {
    let mut em = Emitter::new(module_name);
    // Precompute record layouts (structs/unions) and globals
    em.set_layouts(tu);
    em.emit_globals(tu)?;
    for f in &tu.functions {
        em.emit_function(f)?;
    }
    Ok(em.finish())
}

// Simple record layout structs for backend lowering
#[derive(Debug, Clone)]
struct StructLayout { size: usize, align: usize, members: HashMap<String, (usize, Type)> }
#[derive(Debug, Clone)]
struct UnionLayout { size: usize, align: usize, members: HashMap<String, Type> }

struct Emitter {
    module_name: String,
    // text buffers
    buf: String,              // function bodies
    decls: Vec<String>,       // declare lines
    decls_seen: HashSet<String>,
    globals: Vec<String>,     // global constants/vars
    // Map of global names to their types for identifier resolution
    global_types: HashMap<String, Type>,

    // Record layouts
    struct_layouts: HashMap<String, StructLayout>,
    union_layouts: HashMap<String, UnionLayout>,

    // string pool: decoded bytes -> (global name, len)
    str_pool: HashMap<Vec<u8>, (String, usize)>,
    next_str_id: usize,

    // per-function state (reset at each function)
    tmp: usize,
    label: usize,
    locals: HashMap<String, String>, // name -> %alloca symbol (ptr to storage)
    locals_ty: HashMap<String, Type>,// name -> declared type
    consts: HashMap<String, i32>,    // name -> constant value if known (ints only)
    loop_stack: Vec<(String, String)>, // (break_label, continue_label)
    switch_stack: Vec<String>,       // break targets for switches (reserved)
    in_loop: usize,                  // nesting counter for loops (disables unsafe const folding)
    terminated: bool,
}

impl Emitter {
    fn new(module_name: &str) -> Self {
        Self {
            module_name: module_name.to_string(),
            buf: String::new(),
            decls: Vec::new(),
            decls_seen: HashSet::new(),
            globals: Vec::new(),
            global_types: HashMap::new(),
            struct_layouts: HashMap::new(),
            union_layouts: HashMap::new(),
            str_pool: HashMap::new(),
            next_str_id: 0,
            tmp: 0,
            label: 0,
            locals: HashMap::new(),
            locals_ty: HashMap::new(),
            consts: HashMap::new(),
            loop_stack: Vec::new(),
            switch_stack: Vec::new(),
            in_loop: 0,
            terminated: false,
        }
    }

    fn finish(self) -> String {
        let mut out = String::new();
        let _ = writeln!(&mut out, "; ModuleID = '{}'", self.module_name);
        for d in &self.decls { let _ = writeln!(&mut out, "{}", d); }
        for g in &self.globals { let _ = writeln!(&mut out, "{}", g); }
        out.push_str(&self.buf);
        out
    }

    fn add_decl(&mut self, decl: &str) {
        if self.decls_seen.insert(decl.to_string()) {
            self.decls.push(decl.to_string());
        }
    }

    fn reset_function_state(&mut self) {
        self.tmp = 0;
        self.label = 0;
        self.locals.clear();
        self.locals_ty.clear();
        self.consts.clear();
        self.loop_stack.clear();
        self.switch_stack.clear();
        self.in_loop = 0;
        self.terminated = false;
    }

    fn new_tmp(&mut self) -> String { self.tmp += 1; format!("%t{}", self.tmp) }
    fn new_label(&mut self) -> String { self.label += 1; format!("L{}", self.label) }

    fn start_block(&mut self, label: &str) {
        let _ = writeln!(self.buf, "{}:", label);
        self.terminated = false;
    }

    fn br_uncond(&mut self, target: &str) {
        if self.terminated { return; }
        let _ = writeln!(self.buf, "  br label %{}", target);
        self.terminated = true;
    }

    fn br_cond(&mut self, cond_i1: &str, then_lbl: &str, else_lbl: &str) {
        if self.terminated { return; }
        let _ = writeln!(self.buf, "  br i1 {}, label %{}, label %{}", cond_i1, then_lbl, else_lbl);
        self.terminated = true;
    }

    // ===== Layouts and sizes =====
    fn set_layouts(&mut self, tu: &TranslationUnit) {
        // Build struct layouts
        for r in &tu.records {
            match r.kind {
                RecordKind::Struct => {
                    let mut off = 0usize;
                    let mut max_align = 1usize;
                    let mut map: HashMap<String, (usize, Type)> = HashMap::new();
                    for (name, ty) in &r.members {
                        let a = self.alignof_t(ty);
                        let s = self.sizeof_t_usize(ty);
                        max_align = max_align.max(a);
                        off = round_up(off, a);
                        map.insert(name.clone(), (off, ty.clone()));
                        off = off.saturating_add(s);
                    }
                    let size = round_up(off, max_align.max(1));
                    self.struct_layouts.insert(r.tag.clone(), StructLayout { size, align: max_align.max(1), members: map });
                }
                RecordKind::Union => {
                    let mut size = 0usize;
                    let mut max_align = 1usize;
                    let mut map: HashMap<String, Type> = HashMap::new();
                    for (name, ty) in &r.members {
                        let a = self.alignof_t(ty);
                        let s = self.sizeof_t_usize(ty);
                        max_align = max_align.max(a);
                        size = size.max(s);
                        map.insert(name.clone(), ty.clone());
                    }
                    let size = round_up(size, max_align.max(1));
                    self.union_layouts.insert(r.tag.clone(), UnionLayout { size, align: max_align.max(1), members: map });
                }
            }
        }
    }

    fn sizeof_t_usize(&self, ty: &Type) -> usize {
        match ty {
            Type::Int => 4,
            Type::Void => 0,
            Type::Pointer(_) => 8,
            Type::Array(inner, n) => n.saturating_mul(self.sizeof_t_usize(inner)),
            Type::Struct(tag) => self.struct_layouts.get(tag).map(|l| l.size).unwrap_or(0),
            Type::Union(tag)  => self.union_layouts.get(tag).map(|l| l.size).unwrap_or(0),
            Type::Enum(_) | Type::Named(_) => 4,
        }
    }
    fn sizeof_t(&self, ty: &Type) -> i32 { self.sizeof_t_usize(ty) as i32 }

    fn alignof_t(&self, ty: &Type) -> usize {
        match ty {
            Type::Int => 4,
            Type::Void => 1,
            Type::Pointer(_) => 8,
            Type::Array(inner, _n) => self.alignof_t(inner),
            Type::Struct(tag) => self.struct_layouts.get(tag).map(|l| l.align).unwrap_or(4),
            Type::Union(tag) => self.union_layouts.get(tag).map(|l| l.align).unwrap_or(8),
            Type::Enum(_) | Type::Named(_) => 4,
        }
    }

    // ===== Globals =====
    fn emit_globals(&mut self, tu: &TranslationUnit) -> Result<()> {
        for g in &tu.globals {
            // Track type for identifier resolution inside functions
            self.global_types.insert(g.name.clone(), g.ty.clone());

            let is_extern = matches!(g.storage, Some(parse::ast::Storage::Extern));

            match &g.ty {
                Type::Int => {
                    if is_extern {
                        // Only declare external, do not define
                        let def = format!("@{} = external global i32", g.name);
                        self.globals.push(def);
                    } else {
                        let init_str = if let Some(Expr::IntLiteral(repr)) = &g.init {
                            format!("{}", parse_int_repr(repr))
                        } else if g.init.is_some() {
                            // Non-constant: fallback to 0 for now
                            "0".to_string()
                        } else {
                            "zeroinitializer".to_string()
                        };
                        let def = format!("@{} = global i32 {}", g.name, init_str);
                        self.globals.push(def);
                    }
                }
                Type::Pointer(_) => {
                    if is_extern {
                        let def = format!("@{} = external global ptr", g.name);
                        self.globals.push(def);
                    } else {
                        let init_val = if let Some(init) = &g.init {
                            match init {
                                Expr::StringLiteral(repr) => {
                                    let (sname, len) = self.ensure_string_global_from_repr(repr);
                                    format!("getelementptr inbounds ([{} x i8], ptr {}, i64 0, i64 0)", len, sname)
                                }
                                Expr::Cast { expr, .. } => {
                                    if let Expr::StringLiteral(repr) = &**expr {
                                        let (sname, len) = self.ensure_string_global_from_repr(repr);
                                        format!("getelementptr inbounds ([{} x i8], ptr {}, i64 0, i64 0)", len, sname)
                                    } else { "null".to_string() }
                                }
                                Expr::IntLiteral(s) => {
                                    if parse_int_repr(s) == 0 { "null".to_string() } else { "null".to_string() }
                                }
                                _ => "null".to_string(),
                            }
                        } else { "null".to_string() };
                        let def = format!("@{} = global ptr {}", g.name, init_val);
                        self.globals.push(def);
                    }
                }
                _ => {
                    if is_extern {
                        let def = format!("@{} = external global i32", g.name);
                        self.globals.push(def);
                    } else {
                        let def = format!("@{} = global i32 0", g.name);
                        self.globals.push(def);
                    }
                }
            }
        }
        Ok(())
    }

    // ===== Strings =====
    fn emit_string_ptr(&mut self, repr: &str) -> String {
        let bytes = decode_c_string(repr);
        if let Some((gname, len)) = self.str_pool.get(&bytes).cloned() {
            let tmp = self.new_tmp();
            let _ = writeln!(self.buf, "  {} = getelementptr inbounds [{} x i8], ptr {}, i64 0, i64 0", tmp, len, gname);
            return tmp;
        }
        let len = bytes.len();
        let gname = format!("@.str.{}", self.next_str_id);
        self.next_str_id += 1;
        let enc = llvm_escape_c_bytes(&bytes);
        let def = format!("{} = private unnamed_addr constant [{} x i8] c\"{}\"", gname, len, enc);
        self.globals.push(def);
        self.str_pool.insert(bytes, (gname.clone(), len));
        let tmp = self.new_tmp();
        let _ = writeln!(self.buf, "  {} = getelementptr inbounds [{} x i8], ptr {}, i64 0, i64 0", tmp, len, gname);
        tmp
    }

    // Ensure a string global exists for the given literal repr; return (global_name, len)
    fn ensure_string_global_from_repr(&mut self, repr: &str) -> (String, usize) {
        let bytes = decode_c_string(repr);
        if let Some((gname, len)) = self.str_pool.get(&bytes).cloned() { return (gname, len); }
        let len = bytes.len();
        let gname = format!("@.str.{}", self.next_str_id);
        self.next_str_id += 1;
        let enc = llvm_escape_c_bytes(&bytes);
        let def = format!("{} = private unnamed_addr constant [{} x i8] c\"{}\"", gname, len, enc);
        self.globals.push(def);
        self.str_pool.insert(bytes, (gname.clone(), len));
        (gname, len)
    }

    // ===== Functions =====
    fn emit_function(&mut self, f: &AstFn) -> Result<()> {
        self.reset_function_state();

        // Determine return LLVM type (limited for now)
        let ret_ty = match f.ret_type {
            Type::Int => "i32",
            Type::Void => "void",
            _ => "i32", // treat pointers and other types as i32 for now
        };

        // Emit function header with parameters (all params i32 for now)
        let mut header = String::new();
        let _ = write!(header, "define {} @{}(", ret_ty, f.name);
        for (i, p) in f.params.iter().enumerate() {
            if i > 0 { let _ = write!(header, ", "); }
            let _ = write!(header, "i32 %{}", p.name);
        }
        let _ = write!(header, ") {{");
        let _ = writeln!(self.buf, "{}", header);

        // Prologue: allocate storage for each parameter and store incoming arg
        for p in &f.params {
            let alloca_name = format!("%{}.addr", p.name);
            let _ = writeln!(self.buf, "  {} = alloca i32", alloca_name);
            let _ = writeln!(self.buf, "  store i32 %{}, ptr {}", p.name, alloca_name);
            self.locals.insert(p.name.clone(), alloca_name);
            self.locals_ty.insert(p.name.clone(), Type::Int);
            self.consts.remove(&p.name);
        }

        // Body
        for stmt in &f.body {
            self.emit_stmt(stmt, &f.ret_type);
        }

        if !self.terminated {
            match f.ret_type {
                Type::Void => { let _ = writeln!(self.buf, "  ret void"); }
                _ => { let _ = writeln!(self.buf, "  ret i32 0"); }
            }
        }
        let _ = writeln!(self.buf, "}}");
        Ok(())
    }

    // Always emit an icmp for truthiness; return (i1_ssa, None)
    fn to_bool(&mut self, vstr: String, _vc: Option<i32>) -> (String, Option<bool>) {
        let ctmp = self.new_tmp();
        let _ = writeln!(self.buf, "  {} = icmp ne i32 {}, 0", ctmp, vstr);
        (ctmp, None)
    }

    // Heuristic to determine if an expression yields a pointer value (for casts and ptr arith)
    fn expr_is_pointer(&self, e: &Expr) -> bool {
        match e {
            Expr::StringLiteral(_) => true,
            Expr::Unary { op: UnaryOp::AddrOf, .. } => true,
            // If we know the identifier is a pointer, treat as pointer
            Expr::Ident(name) => matches!(self.locals_ty.get(name), Some(Type::Pointer(_))),
            // Cast target type is a pointer
            Expr::Cast { ty, .. } => matches!(ty, Type::Pointer(_)),
            _ => false,
        }
    }

    // Compute pointer to struct/union member; returns (ptr_to_field, field_type)
    fn emit_member_ptr(&mut self, base: &Expr, field: &str, arrow: bool) -> (String, Type) {
        // Determine base pointer and record type
        let (base_ptr, rec_ty) = if arrow {
            // base is pointer to struct/union; value is a ptr loaded from expression
            let (pv, _pc) = self.emit_expr(base);
            let rty = match base {
                Expr::Ident(n) => self.locals_ty.get(n).cloned().unwrap_or(Type::Pointer(Box::new(Type::Struct(String::new())))),
                _ => Type::Pointer(Box::new(Type::Struct(String::new()))),
            };
            (pv, rty)
        } else {
            // base is an lvalue struct/union; must be local identifier for now
            if let Expr::Ident(n) = base {
                let ptr = self.locals.get(n).cloned().unwrap_or_else(|| "%0".to_string());
                let ty = self.locals_ty.get(n).cloned().unwrap_or(Type::Struct(String::new()));
                (ptr, ty)
            } else {
                ("%0".to_string(), Type::Struct(String::new()))
            }
        };

        match rec_ty {
            Type::Struct(tag) => {
                // Prefetch (offset, type) to avoid overlapping immutable/mutable borrows
                let (off_opt, fty_opt) = {
                    if let Some(sl) = self.struct_layouts.get(&tag) {
                        if let Some((off, fty)) = sl.members.get(field) {
                            (Some(*off), Some(fty.clone()))
                        } else { (None, None) }
                    } else { (None, None) }
                };
                if let (Some(off), Some(fty)) = (off_opt, fty_opt) {
                    let gep = self.new_tmp();
                    let _ = writeln!(self.buf, "  {} = getelementptr inbounds i8, ptr {}, i64 {}", gep, base_ptr, off as i64);
                    return (gep, fty);
                }
                (base_ptr, Type::Int)
            }
            Type::Pointer(inner) => match *inner {
                Type::Struct(ref tag) => {
                    let (off_opt, fty_opt) = {
                        if let Some(sl) = self.struct_layouts.get(tag) {
                            if let Some((off, fty)) = sl.members.get(field) {
                                (Some(*off), Some(fty.clone()))
                            } else { (None, None) }
                        } else { (None, None) }
                    };
                    if let (Some(off), Some(fty)) = (off_opt, fty_opt) {
                        let gep = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = getelementptr inbounds i8, ptr {}, i64 {}", gep, base_ptr, off as i64);
                        return (gep, fty);
                    }
                    (base_ptr, Type::Int)
                }
                Type::Union(ref tag) => {
                    let fty_opt = {
                        if let Some(ul) = self.union_layouts.get(tag) {
                            ul.members.get(field).cloned()
                        } else { None }
                    };
                    if let Some(fty) = fty_opt {
                        let gep = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = getelementptr inbounds i8, ptr {}, i64 0", gep, base_ptr);
                        return (gep, fty);
                    }
                    (base_ptr, Type::Int)
                }
                _ => (base_ptr, Type::Int),
            },
            Type::Union(tag) => {
                let fty_opt = {
                    if let Some(ul) = self.union_layouts.get(&tag) {
                        ul.members.get(field).cloned()
                    } else { None }
                };
                if let Some(fty) = fty_opt {
                    let gep = self.new_tmp();
                    let _ = writeln!(self.buf, "  {} = getelementptr inbounds i8, ptr {}, i64 0", gep, base_ptr);
                    return (gep, fty);
                }
                (base_ptr, Type::Int)
            }
            _ => (base_ptr, Type::Int),
        }
    }

    // returns (value_str, optional_constant_i32)
    fn emit_expr(&mut self, e: &Expr) -> (String, Option<i32>) {
        match e {
            Expr::IntLiteral(repr) => {
                let v = parse_int_repr(repr);
                (format!("{}", v), Some(v))
            }
            Expr::StringLiteral(repr) => {
                let ptr = self.emit_string_ptr(repr);
                (ptr, None)
            }
            Expr::Ident(name) => {
                if let Some(ptr) = self.locals.get(name).cloned() {
                    // Snapshot type to avoid immutable + mutable borrow overlap
                    let lty = self.locals_ty.get(name).cloned();
                    match lty {
                        Some(Type::Int) => {
                            let tmp = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = load i32, ptr {}", tmp, ptr);
                            let c = if self.in_loop == 0 { self.consts.get(name).copied() } else { None };
                            if let Some(v) = c { (format!("{}", v), c) } else { (tmp, None) }
                        }
                        Some(Type::Pointer(_)) => {
                            let tmp = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = load ptr, ptr {}", tmp, ptr);
                            (tmp, None)
                        }
                        Some(Type::Array(_inner, n)) => {
                            // Decay array local to i32* by GEP 0,0 on [N x i32]
                            let dec = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = getelementptr inbounds [{} x i32], ptr {}, i64 0, i64 0", dec, n, ptr);
                            (dec, None)
                        }
                        // Struct/union as rvalue not supported -> return 0
                        Some(Type::Struct(_)) | Some(Type::Union(_)) => ("0".to_string(), Some(0)),
                        _ => ("0".to_string(), Some(0)),
                    }
                } else if let Some(gty) = self.global_types.get(name).cloned() {
                    match gty {
                        Type::Int => {
                            let tmp = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = load i32, ptr @{}", tmp, name);
                            (tmp, None)
                        }
                        Type::Pointer(_) => {
                            let tmp = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = load ptr, ptr @{}", tmp, name);
                            (tmp, None)
                        }
                        Type::Array(_inner, n) => {
                            let dec = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = getelementptr inbounds [{} x i32], ptr @{}, i64 0, i64 0", dec, n, name);
                            (dec, None)
                        }
                        _ => ("0".to_string(), Some(0)),
                    }
                } else {
                    ("0".to_string(), Some(0))
                }
            }
            // Member access: load value of field
            Expr::Member { base, field, arrow } => {
                let (ptr, fty) = self.emit_member_ptr(base, field, *arrow);
                match fty {
                    Type::Pointer(_) => {
                        let tmp = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = load ptr, ptr {}", tmp, ptr);
                        (tmp, None)
                    }
                    _ => {
                        let tmp = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = load i32, ptr {}", tmp, ptr);
                        (tmp, None)
                    }
                }
            }
            Expr::Unary { op, expr } => {
                match op {
                    UnaryOp::Plus => self.emit_expr(expr),
                    UnaryOp::Minus => {
                        let (vstr, vc) = self.emit_expr(expr);
                        match vc {
                            Some(c) => (format!("{}", -c), Some(-c)),
                            None => { let tmp = self.new_tmp(); let _ = writeln!(self.buf, "  {} = sub i32 0, {}", tmp, vstr); (tmp, None) }
                        }
                    }
                    UnaryOp::BitNot => {
                        let (vstr, vc) = self.emit_expr(expr);
                        match vc {
                            Some(c) => (format!("{}", !c), Some(!c)),
                            None => { let tmp = self.new_tmp(); let _ = writeln!(self.buf, "  {} = xor i32 {}, -1", tmp, vstr); (tmp, None) }
                        }
                    }
                    UnaryOp::LogicalNot => {
                        let (vstr, vc) = self.emit_expr(expr);
                        match vc {
                            Some(c) => (format!("{}", if c == 0 {1} else {0}), Some(if c == 0 {1} else {0})),
                            None => { let cmp = self.new_tmp(); let _ = writeln!(self.buf, "  {} = icmp eq i32 {}, 0", cmp, vstr); let z = self.new_tmp(); let _ = writeln!(self.buf, "  {} = zext i1 {} to i32", z, cmp); (z, None) }
                        }
                    }
                    UnaryOp::AddrOf => {
                        match &**expr {
                            Expr::Ident(name) => {
                                if let Some(ptr) = self.locals.get(name).cloned() {
                                    (ptr, None)
                                } else if self.global_types.contains_key(name) {
                                    (format!("@{}", name), None)
                                } else {
                                    ("0".to_string(), Some(0))
                                }
                            }
                            Expr::Member { base, field, arrow } => {
                                let (p, _fty) = self.emit_member_ptr(base, field, *arrow);
                                (p, None)
                            }
                            _ => ("0".to_string(), Some(0)),
                        }
                    }
                    UnaryOp::Deref => {
                        let (pstr, _pc) = self.emit_expr(expr);
                        let tmp = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = load i32, ptr {}", tmp, pstr);
                        (tmp, None)
                    }
                }
            }
            Expr::Binary { op, lhs, rhs } => {
                match op {
                    // Arithmetic and bitwise (with pointer arithmetic for +/-)
                    BinaryOp::Plus | BinaryOp::Minus | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod |
                    BinaryOp::Shl | BinaryOp::Shr | BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor => {
                        // Pointer arithmetic via GEP when mixing ptr and int for +/-
                        if matches!(op, BinaryOp::Plus | BinaryOp::Minus) {
                            let lhs_is_ptr = self.expr_is_pointer(lhs);
                            let rhs_is_ptr = self.expr_is_pointer(rhs);
                            if lhs_is_ptr && !rhs_is_ptr {
                                let (lv_str, _lv_c) = self.emit_expr(lhs);
                                let (rv_str, rv_c) = self.emit_expr(rhs);
                                let idx64 = if let Some(c) = rv_c {
                                    let v: i64 = if matches!(op, BinaryOp::Minus) { -(c as i64) } else { c as i64 };
                                    format!("{}", v)
                                } else {
                                    let z = self.new_tmp();
                                    let _ = writeln!(self.buf, "  {} = zext i32 {} to i64", z, rv_str);
                                    if matches!(op, BinaryOp::Minus) { let neg = self.new_tmp(); let _ = writeln!(self.buf, "  {} = sub i64 0, {}", neg, z); neg } else { z }
                                };
                                let gep = self.new_tmp();
                                let _ = writeln!(self.buf, "  {} = getelementptr inbounds i32, ptr {}, i64 {}", gep, lv_str, idx64);
                                return (gep, None);
                            } else if !lhs_is_ptr && rhs_is_ptr && matches!(op, BinaryOp::Plus) {
                                let (lv_str, lv_c) = self.emit_expr(lhs);
                                let (rv_str, _rv_c) = self.emit_expr(rhs);
                                let idx64 = if let Some(c) = lv_c { format!("{}", c as i64) } else { let z = self.new_tmp(); let _ = writeln!(self.buf, "  {} = zext i32 {} to i64", z, lv_str); z };
                                let gep = self.new_tmp();
                                let _ = writeln!(self.buf, "  {} = getelementptr inbounds i32, ptr {}, i64 {}", gep, rv_str, idx64);
                                return (gep, None);
                            }
                        }
                        // Default integer arithmetic
                        let (lv_str, lv_c) = self.emit_expr(lhs);
                        let (rv_str, rv_c) = self.emit_expr(rhs);
                        match op {
                            BinaryOp::Plus => self.bin_arith("add", lv_str, rv_str, lv_c, rv_c, |a,b| a.wrapping_add(b)),
                            BinaryOp::Minus => self.bin_arith("sub", lv_str, rv_str, lv_c, rv_c, |a,b| a.wrapping_sub(b)),
                            BinaryOp::Mul => self.bin_arith("mul", lv_str, rv_str, lv_c, rv_c, |a,b| a.wrapping_mul(b)),
                            BinaryOp::Div => self.bin_arith("sdiv", lv_str, rv_str, lv_c, rv_c, |a,b| if b!=0 { a.wrapping_div(b) } else { 0 }),
                            BinaryOp::Mod => self.bin_arith("srem", lv_str, rv_str, lv_c, rv_c, |a,b| if b!=0 { a.wrapping_rem(b) } else { 0 }),
                            BinaryOp::Shl => self.bin_arith("shl", lv_str, rv_str, lv_c, rv_c, |a,b| a.wrapping_shl((b as u32) & 31)),
                            BinaryOp::Shr => self.bin_arith("ashr", lv_str, rv_str, lv_c, rv_c, |a,b| (a >> ((b as u32) & 31))),
                            BinaryOp::BitAnd => self.bin_arith("and", lv_str, rv_str, lv_c, rv_c, |a,b| a & b),
                            BinaryOp::BitOr  => self.bin_arith("or",  lv_str, rv_str, lv_c, rv_c, |a,b| a | b),
                            BinaryOp::BitXor => self.bin_arith("xor", lv_str, rv_str, lv_c, rv_c, |a,b| a ^ b),
                            _ => unreachable!(),
                        }
                    }
                    // Logical with i1 and zext to i32 (no short-circuit side effects for now)
                    BinaryOp::LAnd | BinaryOp::LOr => {
                        let (lv_str, lv_c) = self.emit_expr(lhs);
                        let (rv_str, rv_c) = self.emit_expr(rhs);
                        let (lb_str, lb_c) = self.to_bool(lv_str, lv_c);
                        let (rb_str, rb_c) = self.to_bool(rv_str, rv_c);
                        if let (Some(la), Some(rb)) = (lb_c, rb_c) {
                            let v = match op { BinaryOp::LAnd => (la && rb) as i32, BinaryOp::LOr => (la || rb) as i32, _=>0 };
                            (format!("{}", v), Some(v))
                        } else {
                            let tmpb = self.new_tmp();
                            match (lb_c, rb_c) {
                                (Some(la), None) => { let _ = writeln!(self.buf, "  {} = {} i1 {}, {}", tmpb, if matches!(op, BinaryOp::LAnd){"and"} else {"or"}, if la {"true"} else {"false"}, rb_str); },
                                (None, Some(rbv)) => { let _ = writeln!(self.buf, "  {} = {} i1 {}, {}", tmpb, if matches!(op, BinaryOp::LAnd){"and"} else {"or"}, lb_str, if rbv {"true"} else {"false"}); },
                                (None, None) => { let _ = writeln!(self.buf, "  {} = {} i1 {}, {}", tmpb, if matches!(op, BinaryOp::LAnd){"and"} else {"or"}, lb_str, rb_str); },
                                (Some(_), Some(_)) => unreachable!(),
                            }
                            let z = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = zext i1 {} to i32", z, tmpb);
                            (z, None)
                        }
                    }
                    // Comparisons -> icmp + zext to i32
                    BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge | BinaryOp::Eq | BinaryOp::Ne => {
                        let (lv_str, lv_c) = self.emit_expr(lhs);
                        let (rv_str, rv_c) = self.emit_expr(rhs);
                        let pred = match op {
                            BinaryOp::Lt => "slt", BinaryOp::Le => "sle", BinaryOp::Gt => "sgt", BinaryOp::Ge => "sge",
                            BinaryOp::Eq => "eq", BinaryOp::Ne => "ne", _ => unreachable!()
                        };
                        if let (Some(a), Some(b)) = (lv_c, rv_c) {
                            let v = match pred { "slt" => (a < b) as i32, "sle" => (a <= b) as i32, "sgt" => (a > b) as i32, "sge" => (a >= b) as i32, "eq" => (a == b) as i32, _ => (a != b) as i32 };
                            (format!("{}", v), Some(v))
                        } else {
                            let ctmp = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = icmp {} i32 {}, {}", ctmp, pred, lv_str, rv_str);
                            let z = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = zext i1 {} to i32", z, ctmp);
                            (z, None)
                        }
                    }
                }
            }
            // a[i] load: base decays to i32*, then GEP + load
            Expr::Index { base, index } => {
                let (bstr, _bc) = self.emit_expr(base);
                let (istr, ic) = self.emit_expr(index);
                let idx64 = if let Some(c) = ic { format!("{}", c as i64) } else { let z = self.new_tmp(); let _ = writeln!(self.buf, "  {} = zext i32 {} to i64", z, istr); z };
                let eptr = self.new_tmp();
                let _ = writeln!(self.buf, "  {} = getelementptr inbounds i32, ptr {}, i64 {}", eptr, bstr, idx64);
                let val = self.new_tmp();
                let _ = writeln!(self.buf, "  {} = load i32, ptr {}", val, eptr);
                (val, None)
            }
            // Casts: handle int<->ptr and ptr->ptr
            Expr::Cast { ty, expr } => {
                let (vstr, vc) = self.emit_expr(expr);
                match ty {
                    Type::Int => {
                        if let Some(c) = vc {
                            (format!("{}", c), Some(c))
                        } else if self.expr_is_pointer(expr) {
                            let tmp = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = ptrtoint ptr {} to i32", tmp, vstr);
                            (tmp, None)
                        } else {
                            (vstr, vc)
                        }
                    }
                    Type::Pointer(_) => {
                        if self.expr_is_pointer(expr) {
                            let tmp = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = bitcast ptr {} to ptr", tmp, vstr);
                            (tmp, None)
                        } else {
                            let tmp = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = inttoptr i32 {} to ptr", tmp, vstr);
                            (tmp, None)
                        }
                    }
                    _ => {
                        (vstr, None)
                    }
                }
            }
            // Lowering for conditional operator: cond ? then_e : else_e
            Expr::Cond { cond, then_e, else_e } => {
                let (cv_str, cv_c) = self.emit_expr(cond);
                let (c_i1, _c_b) = self.to_bool(cv_str, cv_c);
                let then_lbl = self.new_label();
                let else_lbl = self.new_label();
                let cont_lbl = self.new_label();
                let res_ptr = self.new_tmp();
                let _ = writeln!(self.buf, "  {} = alloca i32", res_ptr);
                self.br_cond(&c_i1, &then_lbl, &else_lbl);
                self.start_block(&then_lbl);
                let (tv, _tc) = self.emit_expr(then_e);
                let _ = writeln!(self.buf, "  store i32 {}, ptr {}", tv, res_ptr);
                self.br_uncond(&cont_lbl);
                self.start_block(&else_lbl);
                let (ev, _ec) = self.emit_expr(else_e);
                let _ = writeln!(self.buf, "  store i32 {}, ptr {}", ev, res_ptr);
                self.br_uncond(&cont_lbl);
                self.start_block(&cont_lbl);
                let res_ssa = self.new_tmp();
                let _ = writeln!(self.buf, "  {} = load i32, ptr {}", res_ssa, res_ptr);
                (res_ssa, None)
            }
            Expr::Call { callee, args } => {
                if callee == "puts" && args.len() == 1 {
                    self.add_decl("declare i32 @puts(ptr)");
                    let mut arg_strs: Vec<String> = Vec::new();
                    match &args[0] {
                        Expr::StringLiteral(repr) => { let p = self.emit_string_ptr(repr); arg_strs.push(format!("ptr {}", p)); }
                        other => { let (v, _c) = self.emit_expr(other); arg_strs.push(format!("i32 {}", v)); }
                    }
                    let tmp = self.new_tmp();
                    let _ = write!(self.buf, "  {} = call i32 @{}(", tmp, callee);
                    for (i, a) in arg_strs.iter().enumerate() { let _ = write!(self.buf, "{}{}", a, if i + 1 < arg_strs.len() { ", " } else { "" }); }
                    let _ = writeln!(self.buf, ")");
                    (tmp, None)
                } else {
                    let mut arg_vals: Vec<String> = Vec::new();
                    for a in args { let (s, _c) = self.emit_expr(a); arg_vals.push(s); }
                    // Ensure external declaration for callee only if not already defined in this module
                    let already_defined = self.buf.contains(&format!("define i32 @{}(", callee));
                    if !already_defined {
                        let mut decl = format!("declare i32 @{}(", callee);
                        for i in 0..arg_vals.len() {
                            if i > 0 { decl.push_str(", "); }
                            decl.push_str("i32");
                        }
                        decl.push(')');
                        self.add_decl(&decl);
                    }
                    let tmp = self.new_tmp();
                    let _ = write!(self.buf, "  {} = call i32 @{}(", tmp, callee);
                    for (i, av) in arg_vals.iter().enumerate() { let _ = write!(self.buf, "i32 {}{}", av, if i + 1 < arg_vals.len() {", "} else {""}); }
                    let _ = writeln!(self.buf, ")");
                    (tmp, None)
                }
            }
            Expr::IncDec { pre, inc, target } => {
                match &**target {
                    Expr::Ident(name) => {
                        let ptr = if let Some(p) = self.locals.get(name) { p.clone() } else {
                            let p = format!("%{}", name);
                            let _ = writeln!(self.buf, "  {} = alloca i32", p);
                            self.locals.insert(name.clone(), p.clone());
                            self.locals_ty.insert(name.clone(), Type::Int);
                            p
                        };
                        let old = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = load i32, ptr {}", old, ptr);
                        let (newv, _c) = if *inc {
                            self.bin_arith("add", old.clone(), "1".to_string(), None, Some(1), |a,b| a.wrapping_add(b))
                        } else {
                            self.bin_arith("sub", old.clone(), "1".to_string(), None, Some(1), |a,b| a.wrapping_sub(b))
                        };
                        let _ = writeln!(self.buf, "  store i32 {}, ptr {}", newv, ptr);
                        self.consts.remove(name);
                        if *pre { (newv, None) } else { (old, None) }
                    }
                    Expr::Unary { op: UnaryOp::Deref, expr: pexpr } => {
                        let (pstr, _pc) = self.emit_expr(pexpr);
                        let old = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = load i32, ptr {}", old, pstr);
                        let (newv, _c) = if *inc {
                            self.bin_arith("add", old.clone(), "1".to_string(), None, Some(1), |a,b| a.wrapping_add(b))
                        } else {
                            self.bin_arith("sub", old.clone(), "1".to_string(), None, Some(1), |a,b| a.wrapping_sub(b))
                        };
                        let _ = writeln!(self.buf, "  store i32 {}, ptr {}", newv, pstr);
                        self.consts.clear();
                        if *pre { (newv, None) } else { (old, None) }
                    }
                    _ => {
                        let (v, _c) = self.emit_expr(target);
                        (v, None)
                    }
                }
            }
            // Compound assignment: lhs op= rhs
            Expr::AssignOp { op, lhs, rhs } => {
                match &**lhs {
                    Expr::Ident(name) => {
                        let ptr = if let Some(p) = self.locals.get(name) { p.clone() } else {
                            let p = format!("%{}", name);
                            let _ = writeln!(self.buf, "  {} = alloca i32", p);
                            self.locals.insert(name.clone(), p.clone());
                            self.locals_ty.insert(name.clone(), Type::Int);
                            p
                        };
                        let ltmp = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = load i32, ptr {}", ltmp, ptr);
                        let (rv_str, rv_c) = self.emit_expr(rhs);
                        let (res_str, res_c) = match op {
                            BinaryOp::Plus => self.bin_arith("add", ltmp.clone(), rv_str, None, rv_c, |a,b| a.wrapping_add(b)),
                            BinaryOp::Minus => self.bin_arith("sub", ltmp.clone(), rv_str, None, rv_c, |a,b| a.wrapping_sub(b)),
                            BinaryOp::Mul => self.bin_arith("mul", ltmp.clone(), rv_str, None, rv_c, |a,b| a.wrapping_mul(b)),
                            BinaryOp::Div => self.bin_arith("sdiv", ltmp.clone(), rv_str, None, rv_c, |a,b| if b!=0 { a.wrapping_div(b) } else { 0 }),
                            BinaryOp::Mod => self.bin_arith("srem", ltmp.clone(), rv_str, None, rv_c, |a,b| if b!=0 { a.wrapping_rem(b) } else { 0 }),
                            BinaryOp::Shl => self.bin_arith("shl", ltmp.clone(), rv_str, None, rv_c, |a,b| a.wrapping_shl((b as u32) & 31)),
                            BinaryOp::Shr => self.bin_arith("ashr", ltmp.clone(), rv_str, None, rv_c, |a,b| (a >> ((b as u32) & 31))),
                            BinaryOp::BitAnd => self.bin_arith("and", ltmp.clone(), rv_str, None, rv_c, |a,b| a & b),
                            BinaryOp::BitOr  => self.bin_arith("or",  ltmp.clone(), rv_str, None, rv_c, |a,b| a | b),
                            BinaryOp::BitXor => self.bin_arith("xor", ltmp.clone(), rv_str, None, rv_c, |a,b| a ^ b),
                            _ => (ltmp.clone(), None),
                        };
                        let _ = writeln!(self.buf, "  store i32 {}, ptr {}", res_str, ptr);
                        if let Some(c) = res_c { self.consts.insert(name.clone(), c); } else { self.consts.remove(name); }
                        (res_str, res_c)
                    }
                    Expr::Unary { op: UnaryOp::Deref, expr: pexpr } => {
                        let (pstr, _pc) = self.emit_expr(pexpr);
                        let ltmp = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = load i32, ptr {}", ltmp, pstr);
                        let (rv_str, rv_c) = self.emit_expr(rhs);
                        let (res_str, _res_c) = match op {
                            BinaryOp::Plus => self.bin_arith("add", ltmp.clone(), rv_str, None, rv_c, |a,b| a.wrapping_add(b)),
                            BinaryOp::Minus => self.bin_arith("sub", ltmp.clone(), rv_str, None, rv_c, |a,b| a.wrapping_sub(b)),
                            BinaryOp::Mul => self.bin_arith("mul", ltmp.clone(), rv_str, None, rv_c, |a,b| a.wrapping_mul(b)),
                            BinaryOp::Div => self.bin_arith("sdiv", ltmp.clone(), rv_str, None, rv_c, |a,b| if b!=0 { a.wrapping_div(b) } else { 0 }),
                            BinaryOp::Mod => self.bin_arith("srem", ltmp.clone(), rv_str, None, rv_c, |a,b| if b!=0 { a.wrapping_rem(b) } else { 0 }),
                            BinaryOp::Shl => self.bin_arith("shl", ltmp.clone(), rv_str, None, rv_c, |a,b| a.wrapping_shl((b as u32) & 31)),
                            BinaryOp::Shr => self.bin_arith("ashr", ltmp.clone(), rv_str, None, rv_c, |a,b| (a >> ((b as u32) & 31))),
                            BinaryOp::BitAnd => self.bin_arith("and", ltmp.clone(), rv_str, None, rv_c, |a,b| a & b),
                            BinaryOp::BitOr  => self.bin_arith("or",  ltmp.clone(), rv_str, None, rv_c, |a,b| a | b),
                            BinaryOp::BitXor => self.bin_arith("xor", ltmp.clone(), rv_str, None, rv_c, |a,b| a ^ b),
                            _ => (ltmp.clone(), None),
                        };
                        let _ = writeln!(self.buf, "  store i32 {}, ptr {}", res_str, pstr);
                        self.consts.clear();
                        (res_str, None)
                    }
                    _ => {
                        self.emit_expr(rhs)
                    }
                }
            }
            // Sized queries
            Expr::SizeofType(ty) => {
                let sz = self.sizeof_t(ty);
                (format!("{}", sz), Some(sz))
            }
            Expr::SizeofExpr(expr) => {
                let sz = match &**expr {
                    // sizeof on an identifier should use its declared type without array-to-pointer decay
                    Expr::Ident(name) => {
                        match self.locals_ty.get(name) {
                            Some(ty) => self.sizeof_t(ty),
                            None => 4,
                        }
                    }
                    // sizeof string literal = length including NUL terminator
                    Expr::StringLiteral(repr) => decode_c_string(repr).len() as i32,
                    // sizeof(&expr) => pointer size
                    Expr::Unary { op: UnaryOp::AddrOf, .. } => 8,
                    // sizeof(*expr) => sizeof(int) for our supported pointee
                    Expr::Unary { op: UnaryOp::Deref, .. } => 4,
                    // sizeof on a cast expression uses the target type
                    Expr::Cast { ty, .. } => self.sizeof_t(ty),
                    // sizeof on an indexing expression yields element size (int)
                    Expr::Index { .. } => 4,
                    // Fallback: use pointer heuristic vs int
                    _ => { if self.expr_is_pointer(&**expr) { 8 } else { 4 } }
                };
                (format!("{}", sz), Some(sz))
            }
            // Comma operator: evaluate LHS for side effects, then RHS yields the value
            Expr::Comma { lhs, rhs } => {
                let (_ls, _lc) = self.emit_expr(lhs);
                let (rs, rc) = self.emit_expr(rhs);
                (rs, rc)
            }
            // Simple assignment to lvalue (identifier already handled above)
            Expr::Assign { name, value } => {
                let (vstr, vc) = self.emit_expr(value);
                let ptr = if let Some(p) = self.locals.get(name) { p.clone() } else {
                    let p = format!("%{}", name);
                    let _ = writeln!(self.buf, "  {} = alloca i32", p);
                    self.locals.insert(name.clone(), p.clone());
                    self.locals_ty.insert(name.clone(), Type::Int);
                    p
                };
                match self.locals_ty.get(name) {
                    Some(Type::Pointer(_)) => {
                        let _ = writeln!(self.buf, "  store ptr {}, ptr {}", vstr, ptr);
                        self.consts.remove(name);
                    }
                    _ => {
                        let _ = writeln!(self.buf, "  store i32 {}, ptr {}", vstr, ptr);
                        if let Some(c) = vc { self.consts.insert(name.clone(), c); } else { self.consts.remove(name); }
                    }
                }
                (vstr, vc)
            }
            // Store i32 into *ptr; due to unknown aliasing, invalidate integer constant cache
            Expr::AssignDeref { ptr: pexpr, value } => {
                let (pstr, _pc) = self.emit_expr(pexpr);
                let (vstr, _vc) = self.emit_expr(value);
                let _ = writeln!(self.buf, "  store i32 {}, ptr {}", vstr, pstr);
                self.consts.clear();
                (vstr, None)
            }
        }
    }

    fn bin_arith<F: Fn(i32,i32)->i32>(&mut self, op: &str, l: String, r: String, lc: Option<i32>, rc: Option<i32>, f: F) -> (String, Option<i32>) {
        if let (Some(a), Some(b)) = (lc, rc) { return (format!("{}", f(a,b)), Some(f(a,b))); }
        let tmp = self.new_tmp();
        let _ = writeln!(self.buf, "  {} = {} i32 {}, {}", tmp, op, l, r);
        (tmp, None)
    }

    fn emit_stmt(&mut self, s: &Stmt, ret_ty: &Type) {
        match s {
            Stmt::Block(stmts) => {
                if self.terminated { return; }
                for st in stmts { self.emit_stmt(st, ret_ty); if self.terminated { break; } }
            }
            Stmt::If { cond, then_branch, else_branch } => {
                if self.terminated { return; }
                let (cv_str, cv_c) = self.emit_expr(cond);
                let (c_i1, _c_b) = self.to_bool(cv_str, cv_c);
                let then_lbl = self.new_label();
                let cont_lbl = self.new_label();
                let else_lbl = if else_branch.is_some() { Some(self.new_label()) } else { None };
                if let Some(el) = &else_lbl {
                    self.br_cond(&c_i1, &then_lbl, el);
                } else {
                    self.br_cond(&c_i1, &then_lbl, &cont_lbl);
                }
                // then
                self.start_block(&then_lbl);
                for st in then_branch { self.emit_stmt(st, ret_ty); if self.terminated { break; } }
                if !self.terminated { self.br_uncond(&cont_lbl); }

                // else
                if let Some(el) = else_lbl {
                    self.start_block(&el);
                    if let Some(eb) = else_branch {
                        for st in eb { self.emit_stmt(st, ret_ty); if self.terminated { break; } }
                    }
                    if !self.terminated { self.br_uncond(&cont_lbl); }
                }

                // cont
                self.start_block(&cont_lbl);
            },
            Stmt::While { cond, body } => {
                if self.terminated { return; }
                let cond_lbl = self.new_label();
                let body_lbl = self.new_label();
                let end_lbl  = self.new_label();
                // enter loop context before evaluating condition
                self.loop_stack.push((end_lbl.clone(), cond_lbl.clone()));
                self.in_loop += 1;
                self.br_uncond(&cond_lbl);
                self.start_block(&cond_lbl);
                let (cv_str, cv_c) = self.emit_expr(cond);
                let (c_i1, _c_b) = self.to_bool(cv_str, cv_c);
                self.br_cond(&c_i1, &body_lbl, &end_lbl);
                self.start_block(&body_lbl);
                for st in body { self.emit_stmt(st, ret_ty); if self.terminated { break; } }
                if !self.terminated { self.br_uncond(&cond_lbl); }
                // exit loop context
                self.in_loop -= 1;
                let _ = self.loop_stack.pop();
                self.start_block(&end_lbl);
            }
            Stmt::DoWhile { body, cond } => {
                if self.terminated { return; }
                let body_lbl = self.new_label();
                let cond_lbl = self.new_label();
                let end_lbl  = self.new_label();
                // enter loop context before executing body (at-least-once semantics)
                self.loop_stack.push((end_lbl.clone(), cond_lbl.clone()));
                self.in_loop += 1;
                self.br_uncond(&body_lbl);
                self.start_block(&body_lbl);
                for st in body { self.emit_stmt(st, ret_ty); if self.terminated { break; } }
                if !self.terminated { self.br_uncond(&cond_lbl); }
                self.start_block(&cond_lbl);
                let (cv_str, cv_c) = self.emit_expr(cond);
                let (c_i1, _c_b) = self.to_bool(cv_str, cv_c);
                self.br_cond(&c_i1, &body_lbl, &end_lbl);
                // exit loop context
                self.in_loop -= 1;
                let _ = self.loop_stack.pop();
                self.start_block(&end_lbl);
            }
            Stmt::For { init, cond, post, body } => {
                if self.terminated { return; }
                if let Some(e) = init { let _ = self.emit_expr(e); }
                let cond_lbl = self.new_label();
                let body_lbl = self.new_label();
                let post_lbl = self.new_label();
                let end_lbl  = self.new_label();
                // enter loop context before evaluating condition
                self.loop_stack.push((end_lbl.clone(), post_lbl.clone()));
                self.in_loop += 1;
                self.br_uncond(&cond_lbl);
                self.start_block(&cond_lbl);
                if let Some(c) = cond {
                    let (cv_str, cv_c) = self.emit_expr(c);
                    let (c_i1, _c_b) = self.to_bool(cv_str, cv_c);
                    self.br_cond(&c_i1, &body_lbl, &end_lbl);
                } else {
                    self.br_uncond(&body_lbl);
                }
                self.start_block(&body_lbl);
                for st in body { self.emit_stmt(st, ret_ty); if self.terminated { break; } }
                if !self.terminated { self.br_uncond(&post_lbl); }
                self.start_block(&post_lbl);
                if let Some(p) = post { let _ = self.emit_expr(p); }
                self.br_uncond(&cond_lbl);
                self.start_block(&end_lbl);
            }
            Stmt::Switch { cond, body } => {
                if self.terminated { return; }
                // Evaluate switch condition once
                let (cstr, _cc) = self.emit_expr(cond);
                let end_lbl = self.new_label();
                let dispatch_lbl = self.new_label();

                // Discover labels in source order and collect cases/default
                let mut labels: Vec<(String, Option<&Expr>)> = Vec::new();
                let mut label_indices: Vec<usize> = Vec::new();
                for (i, s2) in body.iter().enumerate() {
                    match s2 {
                        Stmt::Case { value } => { let l = self.new_label(); labels.push((l, Some(value))); label_indices.push(i); }
                        Stmt::Default => { let l = self.new_label(); labels.push((l, None)); label_indices.push(i); }
                        _ => {}
                    }
                }

                // First block: jump to dispatch
                self.br_uncond(&dispatch_lbl);

                // Emit case/default blocks and fallthrough bodies
                let mut block_starts: HashMap<usize, String> = HashMap::new();
                for (i, idx) in label_indices.iter().enumerate() {
                    let lbl = labels[i].0.clone();
                    block_starts.insert(*idx, lbl);
                }

                // Emit blocks for each label and following statements until next label or end
                let mut i = 0;
                while i < body.len() {
                    if let Some(lbl) = block_starts.get(&i).cloned() {
                        self.start_block(&lbl);
                        // Emit statements until next label or end or break
                        i += 1;
                        while i < body.len() {
                            if block_starts.contains_key(&i) { break; }
                            if let Stmt::Break = body[i] { self.br_uncond(&end_lbl); i += 1; break; }
                            self.emit_stmt(&body[i], ret_ty);
                            i += 1;
                        }
                        if !self.terminated { self.br_uncond(&end_lbl); }
                        continue;
                    }
                    i += 1;
                }

                // Dispatch block: compare and branch to labels in order
                self.start_block(&dispatch_lbl);
                let mut jumped = false;
                for (lbl, val) in &labels {
                    if let Some(vexpr) = val {
                        let (val_str, cval) = self.emit_expr(vexpr);
                        if let Some(c) = cval {
                            let cmp = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = icmp eq i32 {}, {}", cmp, cstr, c);
                            let next_lbl = self.new_label();
                            self.br_cond(&cmp, lbl, &next_lbl);
                            self.start_block(&next_lbl);
                        } else {
                            let cmp = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = icmp eq i32 {}, {}", cmp, cstr, val_str);
                            let next_lbl = self.new_label();
                            self.br_cond(&cmp, lbl, &next_lbl);
                            self.start_block(&next_lbl);
                        }
                        jumped = true;
                    } else {
                        // default label target if no previous match
                        if !jumped { self.br_uncond(lbl); jumped = true; }
                    }
                }
                if !jumped { self.br_uncond(&end_lbl); }
                self.start_block(&end_lbl);
            }
            Stmt::Break => {
                if let Some((break_lbl, _cont_lbl)) = self.loop_stack.last().cloned().or_else(|| self.switch_stack.last().map(|l| (l.clone(), String::new()))) {
                    self.br_uncond(&break_lbl);
                }
            }
            Stmt::Continue => {
                if let Some((_break_lbl, cont_lbl)) = self.loop_stack.last().cloned() {
                    self.br_uncond(&cont_lbl);
                }
            }
            Stmt::Return(e) => {
                if self.terminated { return; }
                let (val_str, _cval) = self.emit_expr(e);
                match ret_ty {
                    Type::Void => { let _ = writeln!(self.buf, "  ret void"); }
                    _ => { let _ = writeln!(self.buf, "  ret i32 {}", val_str); }
                }
                self.terminated = true;
            }
            Stmt::Decl { name, ty, init } => {
                // Declare local with storage type derived from declared type
                let alloca_name = format!("%{}", name);
                match ty {
                    Type::Array(inner, n) => {
                        // Array local: allocate [N x i32]; support only int element for now
                        let _ = writeln!(self.buf, "  {} = alloca [{} x i32]", alloca_name, n);
                        self.locals.insert(name.clone(), alloca_name.clone());
                        self.locals_ty.insert(name.clone(), Type::Array(inner.clone(), *n));
                        // No initializer lowering for arrays yet
                        self.consts.remove(name);
                    }
                    Type::Pointer(inner) => {
                        // Pointer local: allocate ptr and store pointer value; keep precise inner type
                        let _ = writeln!(self.buf, "  {} = alloca ptr", alloca_name);
                        self.locals.insert(name.clone(), alloca_name.clone());
                        self.locals_ty.insert(name.clone(), Type::Pointer(inner.clone()));
                        if let Some(e) = init {
                            let (val_str, _cval) = self.emit_expr(e);
                            let _ = writeln!(self.buf, "  store ptr {}, ptr {}", val_str, alloca_name);
                        }
                        self.consts.remove(name);
                    }
                    Type::Struct(tag) => {
                        let sz = self.struct_layouts.get(tag).map(|l| l.size).unwrap_or(8);
                        let _ = writeln!(self.buf, "  {} = alloca i8, i64 {}", alloca_name, sz);
                        self.locals.insert(name.clone(), alloca_name.clone());
                        self.locals_ty.insert(name.clone(), Type::Struct(tag.clone()));
                        if let Some(_e) = init { /* aggregate init not supported yet */ }
                        self.consts.remove(name);
                    }
                    Type::Union(tag) => {
                        let sz = self.union_layouts.get(tag).map(|l| l.size).unwrap_or(8);
                        let _ = writeln!(self.buf, "  {} = alloca i8, i64 {}", alloca_name, sz);
                        self.locals.insert(name.clone(), alloca_name.clone());
                        self.locals_ty.insert(name.clone(), Type::Union(tag.clone()));
                        if let Some(_e) = init { /* aggregate init not supported yet */ }
                        self.consts.remove(name);
                    }
                    _ => {
                        // Integer (and other non-pointer for now): allocate i32 and store integer value
                        let _ = writeln!(self.buf, "  {} = alloca i32", alloca_name);
                        self.locals.insert(name.clone(), alloca_name.clone());
                        self.locals_ty.insert(name.clone(), Type::Int);
                        if let Some(e) = init {
                            let (val_str, cval) = self.emit_expr(e);
                            let _ = writeln!(self.buf, "  store i32 {}, ptr {}", val_str, alloca_name);
                            if let Some(c) = cval { self.consts.insert(name.clone(), c); } else { self.consts.remove(name); }
                        }
                    }
                }
            }
            Stmt::ExprStmt(e) => { let _ = self.emit_expr(e); }
            // No-op runtime statements
            Stmt::Case { .. } => { /* handled within Switch lowering */ }
            Stmt::Default => { /* handled within Switch lowering */ }
            Stmt::Typedef { .. } => { /* no runtime effect */ }
        }
    }
}

fn round_up(x: usize, a: usize) -> usize { if a == 0 { x } else { (x + a - 1) / a * a } }

fn parse_int_repr(repr: &str) -> i32 {
    if let Some(hex) = repr.strip_prefix("0x").or_else(|| repr.strip_prefix("0X")) {
        i32::from_str_radix(hex, 16).unwrap_or(0)
    } else if repr.len() > 1 && repr.starts_with('0') {
        i32::from_str_radix(&repr[1..], 8).unwrap_or_else(|_| repr.parse::<i32>().unwrap_or(0))
    } else {
        repr.parse::<i32>().unwrap_or(0)
    }
}

fn decode_c_string(repr: &str) -> Vec<u8> {
    // repr includes quotes
    let mut bytes: Vec<u8> = Vec::new();
    let mut it = repr.chars();
    let _ = it.next(); // opening quote
    let mut esc = false;
    let mut hex_mode = false;
    let mut hex_acc = String::new();
    while let Some(ch) = it.next() {
        if hex_mode {
            if ch == '"' { break; }
            if ch.is_ascii_hexdigit() { hex_acc.push(ch); if hex_acc.len() >= 2 { let v = u8::from_str_radix(&hex_acc, 16).unwrap_or(0); bytes.push(v); hex_mode = false; hex_acc.clear(); } }
            else { let v = u8::from_str_radix(&hex_acc, 16).unwrap_or(0); bytes.push(v); hex_mode = false; hex_acc.clear(); if ch == '"' { break; } else { bytes.push(ch as u8); } }
            continue;
        }
        if esc {
            match ch {
                'n' => bytes.push(b'\n'),
                'r' => bytes.push(b'\r'),
                't' => bytes.push(b'\t'),
                '0' => bytes.push(0),
                'x' => { hex_mode = true; }
                '\\' => bytes.push(b'\\'),
                '\'' => bytes.push(b'\''),
                '"' => bytes.push(b'"'),
                _ => bytes.push(ch as u8),
            }
            esc = false;
            continue;
        }
        if ch == '"' { break; }
        if ch == '\\' { esc = true; continue; }
        bytes.push(ch as u8);
    }
    bytes.push(0); // C string NUL-termination
    bytes
}

fn llvm_escape_c_bytes(bytes: &[u8]) -> String {
    let mut s = String::new();
    for &b in bytes {
        match b {
            b'\n' => s.push_str("\\0A"),
            b'\r' => s.push_str("\\0D"),
            b'\t' => s.push_str("\\09"),
            0 => s.push_str("\\00"),
            b'\\' => s.push_str("\\5C"),
            b'\"' => s.push_str("\\22"),
            32..=126 => s.push(b as char),
            _ => s.push_str(&format!("\\{:02X}", b)),
        }
    }
    s
}

pub fn verify_llvm_text(ir: &str) -> anyhow::Result<()> {
    use anyhow::anyhow;
    use std::collections::HashSet;

    let mut label_defs: HashSet<String> = HashSet::new();
    let mut branch_targets: Vec<String> = Vec::new();
    let mut in_block = false;
    let mut saw_term = false;

    for raw in ir.lines() {
        let line = raw.trim();
        if line.is_empty() { continue; }
        if line.starts_with(';') { continue; }

        if line.starts_with("define ") {
            // starting a new function, reset state
            label_defs.clear();
            branch_targets.clear();
            in_block = false;
            saw_term = false;
            continue;
        }
        if line == "}" {
            // end of function: check undefined labels within function
            for tgt in &branch_targets {
                if !label_defs.contains(tgt) {
                    return Err(anyhow!("undefined label: {}", tgt));
                }
            }
            // prepare for possible next function
            label_defs.clear();
            branch_targets.clear();
            in_block = false;
            saw_term = false;
            continue;
        }

        // Label definition: e.g., entry: or L1:
        if line.ends_with(':') {
            let name = line.trim_end_matches(':').to_string();
            if in_block && !saw_term {
                return Err(anyhow!("missing terminator before next label: {}", name));
            }
            in_block = true;
            saw_term = false;
            label_defs.insert(name);
            continue;
        }

        if !in_block {
            // Ignore non-block lines (prologue, decls, etc.)
            continue;
        }

        // Detect terminators and collect branch targets
        if line.starts_with("ret ") {
            if saw_term { return Err(anyhow!("multiple terminators in block")); }
            saw_term = true;
            continue;
        }
        if line.starts_with("br ") {
            if saw_term { return Err(anyhow!("multiple terminators in block")); }
            // collect targets
            // br label %X
            if let Some(idx) = line.find("label %") {
                let rest = &line[idx + "label %".len()..];
                let mut parts = rest.split(|c| c == ',' || c == ' ');
                if let Some(t) = parts.next() {
                    let t = t.trim();
                    if !t.is_empty() { branch_targets.push(t.to_string()); }
                }
                // br i1 ..., label %T, label %E
                if let Some(idx2) = line.rfind("label %") {
                    if idx2 != idx {
                        let rest2 = &line[idx2 + "label %".len()..];
                        let t2 = rest2.split(|c| c == ',' || c == ' ').next().unwrap_or("").trim();
                        if !t2.is_empty() { branch_targets.push(t2.to_string()); }
                    }
                }
            }
            saw_term = true;
            continue;
        }

        // Any other instruction after a terminator within the same block is invalid
        if saw_term {
            return Err(anyhow!("instruction after terminator"));
        }
    }

    // If file/function didn't close with }, still verify targets seen so far
    for tgt in &branch_targets {
        if !label_defs.contains(tgt) {
            return Err(anyhow!("undefined label: {}", tgt));
        }
    }
    Ok(())
}