use anyhow::Result;
use parse::ast::{
    BinaryOp, Expr, Function as AstFn, RecordKind, Stmt, TranslationUnit, Type, UnaryOp,
};
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
struct StructLayout {
    size: usize,
    align: usize,
    members: HashMap<String, (usize, Type)>,
}
#[derive(Debug, Clone)]
struct UnionLayout {
    size: usize,
    align: usize,
    members: HashMap<String, Type>,
}

struct Emitter {
    module_name: String,
    // text buffers
    buf: String,        // function bodies
    decls: Vec<String>, // declare lines
    decls_seen: HashSet<String>,
    globals: Vec<String>, // global constants/vars
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
    locals: HashMap<String, String>, // name -> %alloca symbol (ptr to storage) or @global for static locals
    locals_ty: HashMap<String, Type>, // name -> declared type
    consts: HashMap<String, i32>,    // name -> constant value if known (ints only)
    loop_stack: Vec<(String, String)>, // (break_label, continue_label)
    switch_stack: Vec<String>,       // break targets for switches (reserved)
    in_loop: usize,                  // nesting counter for loops (disables unsafe const folding)
    terminated: bool,
    // New: goto/labels support
    user_labels: HashMap<String, String>, // C label name -> LLVM label name
    in_block: bool,                       // whether a basic block has started

    // Current function name (for static local mangling)
    current_fn: String,
    // Emitted static locals to avoid duplicate global emission
    static_locals_emitted: HashSet<String>,
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
            user_labels: HashMap::new(),
            in_block: false,
            current_fn: String::new(),
            static_locals_emitted: HashSet::new(),
        }
    }

    fn finish(self) -> String {
        let mut out = String::new();
        let _ = writeln!(&mut out, "; ModuleID = '{}'", self.module_name);
        for d in &self.decls {
            let _ = writeln!(&mut out, "{}", d);
        }
        for g in &self.globals {
            let _ = writeln!(&mut out, "{}", g);
        }
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
        self.user_labels.clear();
        self.in_block = false;
        // do not clear current_fn or static_locals_emitted here
    }

    fn new_tmp(&mut self) -> String {
        self.tmp += 1;
        format!("%tmp{}", self.tmp)
    }
    fn new_label(&mut self) -> String {
        self.label += 1;
        format!("L{}", self.label)
    }

    // Ensure/lookup LLVM label name for a given C label
    fn ensure_user_label(&mut self, name: &str) -> String {
        if let Some(lbl) = self.user_labels.get(name).cloned() {
            lbl
        } else {
            let l = self.new_label();
            self.user_labels.insert(name.to_string(), l.clone());
            l
        }
    }

    fn start_block(&mut self, label: &str) {
        let _ = writeln!(self.buf, "{}:", label);
        self.terminated = false;
        self.in_block = true;
    }

    fn br_uncond(&mut self, target: &str) {
        if self.terminated {
            return;
        }
        let _ = writeln!(self.buf, "  br label %{}", target);
        self.terminated = true;
    }

    fn br_cond(&mut self, cond_i1: &str, then_lbl: &str, else_lbl: &str) {
        if self.terminated {
            return;
        }
        let _ = writeln!(
            self.buf,
            "  br i1 {}, label %{}, label %{}",
            cond_i1, then_lbl, else_lbl
        );
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
                    self.struct_layouts.insert(
                        r.tag.clone(),
                        StructLayout {
                            size,
                            align: max_align.max(1),
                            members: map,
                        },
                    );
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
                    self.union_layouts.insert(
                        r.tag.clone(),
                        UnionLayout {
                            size,
                            align: max_align.max(1),
                            members: map,
                        },
                    );
                }
            }
        }
    }

    fn sizeof_t_usize(&self, ty: &Type) -> usize {
        match ty {
            // C89 integers
            Type::Char | Type::SChar | Type::UChar => 1,
            Type::Short | Type::UShort => 2,
            // Project assumption: int and long are 4 bytes
            Type::Int | Type::UInt | Type::Long | Type::ULong => 4,
            Type::Void => 0,
            Type::Pointer(_) => 8,
            Type::Array(inner, n) => n.saturating_mul(self.sizeof_t_usize(inner)),
            Type::Struct(tag) => self.struct_layouts.get(tag).map(|l| l.size).unwrap_or(0),
            Type::Union(tag) => self.union_layouts.get(tag).map(|l| l.size).unwrap_or(0),
            Type::Func { .. } => 0,
            Type::Enum(_) | Type::Named(_) => 4,
        }
    }
    fn sizeof_t(&self, ty: &Type) -> i32 {
        self.sizeof_t_usize(ty) as i32
    }

    fn alignof_t(&self, ty: &Type) -> usize {
        match ty {
            // C89 integers
            Type::Char | Type::SChar | Type::UChar => 1,
            Type::Short | Type::UShort => 2,
            // int/long align to 4 on this target
            Type::Int | Type::UInt | Type::Long | Type::ULong => 4,
            Type::Void => 1,
            Type::Pointer(_) => 8,
            Type::Array(inner, _n) => self.alignof_t(inner),
            Type::Struct(tag) => self.struct_layouts.get(tag).map(|l| l.align).unwrap_or(4),
            Type::Union(tag) => self.union_layouts.get(tag).map(|l| l.align).unwrap_or(8),
            Type::Func { .. } => 1,
            Type::Enum(_) | Type::Named(_) => 4,
        }
    }

    fn emit_globals(&mut self, tu: &TranslationUnit) -> Result<()> {
        use parse::ast::Storage;
        #[derive(Clone)]
        struct Chosen {
            name: String,
            ty: Type,
            storage: Option<Storage>,
            init: Option<Expr>,
        }
        fn prio(storage: &Option<Storage>, init: &Option<Expr>) -> i32 {
            match storage {
                Some(Storage::Extern) => 1, // lowest priority
                _ => {
                    if init.is_some() {
                        3
                    } else {
                        2
                    }
                } // def with init > tentative
            }
        }

        // Helper: parse constant int from Expr (fallback 0)
        fn expr_to_i32(e: &Expr) -> i32 {
            match e {
                Expr::IntLiteral(repr) => parse_int_repr(repr),
                _ => 0,
            }
        }

        // Helper: format [N x i32] for 1D int arrays
        let fmt_i32_arr_ty = |n: usize| -> String { format!("[{} x i32]", n) };

        // Helper: format [N x i8] for char arrays
        let fmt_i8_arr_ty = |n: usize| -> String { format!("[{} x i8]", n) };

        // Helper: build constant for 1D int array from items; zero-fill to len
        let build_i32_array_vals = |items: &Vec<Expr>, len: usize| -> String {
            let mut parts: Vec<String> = Vec::new();
            for i in 0..len {
                let v = if i < items.len() { expr_to_i32(&items[i]) } else { 0 };
                parts.push(format!("i32 {}", v));
            }
            format!("[ {} ]", parts.join(", "))
        };

        // Helper: build constant for 2D int array [[cols x i32] [...], ...]
        let build_i32_array_2d_vals = |rows_expr: &Vec<Expr>, rows: usize, cols: usize| -> String {
            let inner_ty = fmt_i32_arr_ty(cols);
            let mut row_consts: Vec<String> = Vec::new();
            for r in 0..rows {
                let row_items: Vec<Expr> = if r < rows_expr.len() {
                    if let Expr::InitList(vs) = &rows_expr[r] { vs.clone() } else { Vec::new() }
                } else {
                    Vec::new()
                };
                let mut elems: Vec<String> = Vec::new();
                for c in 0..cols {
                    let v = if c < row_items.len() { expr_to_i32(&row_items[c]) } else { 0 };
                    elems.push(format!("i32 {}", v));
                }
                row_consts.push(format!("{} [ {} ]", inner_ty, elems.join(", ")));
            }
            format!("[ {} ]", row_consts.join(", "))
        };

        // Helper: build constant bytes for char arrays. Prefer c"..." if exact length, else explicit list.
        let build_i8_bytes = |bytes: Vec<u8>, target_len: usize| -> String {
            if bytes.len() == target_len {
                let enc = llvm_escape_c_bytes(&bytes);
                format!("c\"{}\"", enc)
            } else {
                let mut parts: Vec<String> = bytes.into_iter().map(|b| format!("i8 {}", b)).collect();
                while parts.len() < target_len { parts.push("i8 0".to_string()); }
                format!("[ {} ]", parts.join(", "))
            }
        };

        // Helper: struct type and value strings for structs with scalar int members.
        let build_struct_ints = |this: &Emitter, tag: &str, items: &Vec<Expr>| -> Option<(String, String)> {
            let sl = this.struct_layouts.get(tag)?;
            // Collect members in offset order
            let mut ordered: Vec<(usize, Type)> = sl
                .members
                .iter()
                .map(|(_n, (off, ty))| (*off, ty.clone()))
                .collect();
            ordered.sort_by_key(|(o, _)| *o);
            let mut ty_parts: Vec<String> = Vec::new();
            let mut val_parts: Vec<String> = Vec::new();
            for (i, (_off, fty)) in ordered.iter().enumerate() {
                match fty {
                    Type::Int | Type::UInt | Type::Long | Type::ULong | Type::Short | Type::UShort | Type::Enum(_) | Type::Named(_) | Type::Char | Type::SChar | Type::UChar => {
                        ty_parts.push("i32".to_string());
                        let v = if i < items.len() { expr_to_i32(&items[i]) } else { 0 };
                        val_parts.push(format!("i32 {}", v));
                    }
                    Type::Pointer(_) => {
                        ty_parts.push("ptr".to_string());
                        // Only allow null for v1; non-null not handled in this helper
                        val_parts.push("ptr null".to_string());
                    }
                    // Not supported in this v1 helper
                    _ => return None,
                }
            }
            Some((format!("{{ {} }}", ty_parts.join(", ")), format!("{{ {} }}", val_parts.join(", "))))
        };

        // First pass: choose exactly one representative per global name
        let mut chosen: HashMap<String, Chosen> = HashMap::new();
        for g in &tu.globals {
            // Track type for identifier resolution inside functions
            self.global_types.insert(g.name.clone(), g.ty.clone());

            let c = Chosen {
                name: g.name.clone(),
                ty: g.ty.clone(),
                storage: g.storage.clone(),
                init: g.init.clone(),
            };
            let cp = prio(&c.storage, &c.init);
            if let Some(prev) = chosen.get(&c.name) {
                let pp = prio(&prev.storage, &prev.init);
                if cp > pp {
                    chosen.insert(c.name.clone(), c);
                }
            } else {
                chosen.insert(c.name.clone(), c);
            }
        }

        // Second pass: emit the selected globals once
        for (_k, g) in chosen {
            let is_extern = matches!(g.storage, Some(Storage::Extern));
            let is_static = matches!(g.storage, Some(Storage::Static));
            let linkage = if is_static { "internal " } else { "" };
            match &g.ty {
                Type::Int => {
                    if is_extern {
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
                        let def = format!("@{} = {}global i32 {}", g.name, linkage, init_str);
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
                                    format!(
                                        "getelementptr inbounds ([{} x i8], ptr {}, i64 0, i64 0)",
                                        len, sname
                                    )
                                }
                                Expr::Cast { expr, .. } => {
                                    if let Expr::StringLiteral(repr) = &**expr {
                                        let (sname, len) = self.ensure_string_global_from_repr(repr);
                                        format!("getelementptr inbounds ([{} x i8], ptr {}, i64 0, i64 0)", len, sname)
                                    } else {
                                        "null".to_string()
                                    }
                                }
                                Expr::IntLiteral(s) => {
                                    if parse_int_repr(s) == 0 { "null".to_string() } else { "null".to_string() }
                                }
                                _ => "null".to_string(),
                            }
                        } else {
                            "null".to_string()
                        };
                        let def = format!("@{} = {}global ptr {}", g.name, linkage, init_val);
                        self.globals.push(def);
                    }
                }
                Type::Array(inner, n) => {
                    // Arrays: support int arrays (1D/2D) and char arrays from string literals.
                    match &**inner {
                        // char-like arrays -> i8 payload
                        Type::Char | Type::SChar | Type::UChar => {
                            let (ty_str, val_str) = if let Some(init) = &g.init {
                                match init {
                                    Expr::StringLiteral(repr) => {
                                        let bytes = decode_c_string(repr);
                                        let target_len = if *n == 0 { bytes.len() } else { *n };
                                        (fmt_i8_arr_ty(target_len), build_i8_bytes(bytes, target_len))
                                    }
                                    Expr::Cast { expr: inner_expr, .. } => {
                                        if let Expr::StringLiteral(repr2) = &**inner_expr {
                                            let bytes = decode_c_string(repr2);
                                            let target_len = if *n == 0 { bytes.len() } else { *n };
                                            (fmt_i8_arr_ty(target_len), build_i8_bytes(bytes, target_len))
                                        } else {
                                            let target_len = if *n == 0 { 0 } else { *n };
                                            let val = if target_len == 0 {
                                                "zeroinitializer".to_string()
                                            } else {
                                                format!("[ {} ]", vec!["i8 0".to_string(); target_len].join(", "))
                                            };
                                            (fmt_i8_arr_ty(target_len), val)
                                        }
                                    }
                                    Expr::InitList(items) => {
                                        let target_len = if *n == 0 { items.len() } else { *n };
                                        let mut bytes: Vec<u8> = Vec::new();
                                        for i in 0..target_len {
                                            bytes.push(if i < items.len() { expr_to_i32(&items[i]) as u8 } else { 0 });
                                        }
                                        (fmt_i8_arr_ty(target_len), build_i8_bytes(bytes, target_len))
                                    }
                                    _ => {
                                        let target_len = if *n == 0 { 0 } else { *n };
                                        let val = if target_len == 0 {
                                            "zeroinitializer".to_string()
                                        } else {
                                            format!("[ {} ]", vec!["i8 0".to_string(); target_len].join(", "))
                                        };
                                        (fmt_i8_arr_ty(target_len), val)
                                    }
                                }
                            } else {
                                let target_len = if *n == 0 { 0 } else { *n };
                                let val = if target_len == 0 {
                                    "zeroinitializer".to_string()
                                } else {
                                    format!("[ {} ]", vec!["i8 0".to_string(); target_len].join(", "))
                                };
                                (fmt_i8_arr_ty(target_len), val)
                            };
                            if is_extern {
                                let def = format!("@{} = external global {}", g.name, ty_str);
                                self.globals.push(def);
                            } else {
                                let def = format!("@{} = {}global {} {}", g.name, linkage, ty_str, val_str);
                                self.globals.push(def);
                            }
                        }
                        // 2D int arrays
                        Type::Array(inner2, n2) if matches!(&**inner2, Type::Int | Type::UInt) => {
                            let rows = if *n == 0 { if let Some(Expr::InitList(vs)) = &g.init { vs.len() } else { 0 } } else { *n };
                            let cols = *n2; // assume sized inner for v1
                            let inner_ty_str = self.llvm_int_array_type_str(&*inner).unwrap_or_else(|| fmt_i32_arr_ty(cols));
                            let ty_str = format!("[{} x {}]", rows, inner_ty_str);
                            let val_str = if let Some(Expr::InitList(rows_items)) = &g.init {
                                build_i32_array_2d_vals(rows_items, rows, cols)
                            } else {
                                let zero_row = format!("{} [ {} ]", inner_ty_str, vec!["i32 0".to_string(); cols].join(", "));
                                format!("[ {} ]", vec![zero_row; rows].join(", "))
                            };
                            if is_extern {
                                let def = format!("@{} = external global {}", g.name, ty_str);
                                self.globals.push(def);
                            } else {
                                let def = format!("@{} = {}global {} {}", g.name, linkage, ty_str, val_str);
                                self.globals.push(def);
                            }
                        }
                        // 1D int arrays
                        Type::Int | Type::UInt | Type::Long | Type::ULong | Type::Short | Type::UShort | Type::Enum(_) | Type::Named(_) => {
                            let len = if *n == 0 { if let Some(Expr::InitList(vs)) = &g.init { vs.len() } else { 0 } } else { *n };
                            let ty_str = fmt_i32_arr_ty(len);
                            let val_str = if let Some(Expr::InitList(items)) = &g.init {
                                build_i32_array_vals(items, len)
                            } else {
                                format!("[ {} ]", vec!["i32 0".to_string(); len].join(", "))
                            };
                            if is_extern {
                                let def = format!("@{} = external global {}", g.name, ty_str);
                                self.globals.push(def);
                            } else {
                                let def = format!("@{} = {}global {} {}", g.name, linkage, ty_str, val_str);
                                self.globals.push(def);
                            }
                        }
                        _ => {
                            // Fallback: treat as byte buffer sized by sizeof_t
                            let total_sz = self.sizeof_t_usize(&g.ty);
                            if is_extern {
                                let def = format!("@{} = external global i8", g.name);
                                self.globals.push(def);
                            } else {
                                let def = format!("@{} = {}global i8 zeroinitializer ; size {} bytes (opaque)", g.name, linkage, total_sz);
                                self.globals.push(def);
                            }
                        }
                    }
                }
                Type::Struct(tag) => {
                    // Structs with scalar int members
                    if is_extern {
                        if let Some((ty_s, _)) = build_struct_ints(self, tag, &Vec::new()) {
                            let def = format!("@{} = external global {}", g.name, ty_s);
                            self.globals.push(def);
                        } else {
                            let def = format!("@{} = external global i32", g.name);
                            self.globals.push(def);
                        }
                    } else {
                        let (ty_s, val_s) = if let Some(Expr::InitList(items)) = &g.init {
                            if let Some((t, v)) = build_struct_ints(self, tag, items) { (t, v) } else { ("i32".to_string(), "zeroinitializer".to_string()) }
                        } else {
                            if let Some((t, v)) = build_struct_ints(self, tag, &Vec::new()) { (t, v) } else { ("i32".to_string(), "zeroinitializer".to_string()) }
                        };
                        let def = format!("@{} = {}global {} {}", g.name, linkage, ty_s, val_s);
                        self.globals.push(def);
                    }
                }
                _ => {
                    if is_extern {
                        let def = format!("@{} = external global i32", g.name);
                        self.globals.push(def);
                    } else {
                        let def = format!("@{} = {}global i32 0", g.name, linkage);
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
            let _ = writeln!(
                self.buf,
                "  {} = getelementptr inbounds [{} x i8], ptr {}, i64 0, i64 0",
                tmp, len, gname
            );
            return tmp;
        }
        let len = bytes.len();
        let gname = format!("@.str.{}", self.next_str_id);
        self.next_str_id += 1;
        let enc = llvm_escape_c_bytes(&bytes);
        let def = format!(
            "{} = private unnamed_addr constant [{} x i8] c\"{}\"",
            gname, len, enc
        );
        self.globals.push(def);
        self.str_pool.insert(bytes, (gname.clone(), len));
        let tmp = self.new_tmp();
        let _ = writeln!(
            self.buf,
            "  {} = getelementptr inbounds [{} x i8], ptr {}, i64 0, i64 0",
            tmp, len, gname
        );
        tmp
    }

    // Ensure a string global exists for the given literal repr; return (global_name, len)
    fn ensure_string_global_from_repr(&mut self, repr: &str) -> (String, usize) {
        let bytes = decode_c_string(repr);
        if let Some((gname, len)) = self.str_pool.get(&bytes).cloned() {
            return (gname, len);
        }
        let len = bytes.len();
        let gname = format!("@.str.{}", self.next_str_id);
        self.next_str_id += 1;
        let enc = llvm_escape_c_bytes(&bytes);
        let def = format!(
            "{} = private unnamed_addr constant [{} x i8] c\"{}\"",
            gname, len, enc
        );
        self.globals.push(def);
        self.str_pool.insert(bytes, (gname.clone(), len));
        (gname, len)
    }

    // ===== Functions =====
    fn emit_function(&mut self, f: &AstFn) -> Result<()> {
        self.reset_function_state();
        self.current_fn = f.name.clone();

        // Determine return LLVM type (limited for now)
        let ret_ty = match f.ret_type {
            Type::Int => "i32",
            Type::Void => "void",
            _ => "i32", // treat pointers and other types as i32 for now
        };

        // Emit function header with parameters (all params i32 for now)
        let pvec = f
            .params
            .iter()
            .map(|p| format!("i32 %{}", p.name))
            .collect::<Vec<_>>();
        let params = if f.variadic {
            if pvec.is_empty() {
                "...".to_string()
            } else {
                format!("{}, ...", pvec.join(", "))
            }
        } else {
            pvec.join(", ")
        };
        let def_kw = if matches!(f.storage, Some(parse::ast::Storage::Static)) {
            "define internal"
        } else {
            "define"
        };
        let _ = writeln!(self.buf, "{} {} @{}({}) {{", def_kw, ret_ty, f.name, params);
        for p in &f.params {
            let alloca_name = format!("%{}.addr", p.name);
            let _ = writeln!(self.buf, "  {} = alloca i32", alloca_name);
            let _ = writeln!(self.buf, "  store i32 %{}, ptr {}", p.name, alloca_name);
            self.locals.insert(p.name.clone(), alloca_name);
            // Track the declared parameter type precisely (Int or UInt or others)
            self.locals_ty.insert(p.name.clone(), p.ty.clone());
            self.consts.remove(&p.name);
        }
        // Body
        for stmt in &f.body {
            self.emit_stmt(stmt, &f.ret_type);
        }

        if !self.terminated {
            match f.ret_type {
                Type::Void => {
                    let _ = writeln!(self.buf, "  ret void");
                }
                _ => {
                    let _ = writeln!(self.buf, "  ret i32 0");
                }
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
            Expr::Unary {
                op: UnaryOp::AddrOf,
                ..
            } => true,
            // Identifiers: treat known pointer locals and arrays (which decay) as pointer-valued
            Expr::Ident(name) => match self.locals_ty.get(name) {
                Some(Type::Pointer(_)) => true,
                Some(Type::Array(_, _)) => true,
                _ => false,
            },
            // Indexing: only pointer-valued if the element type itself is non-scalar (e.g., array/struct/union/pointer)
            Expr::Index { base, .. } => {
                if let Some(bt) = self.type_of_expr(base) {
                    match bt {
                        Type::Array(inner, _) | Type::Pointer(inner) => {
                            match *inner {
                                // Scalar int-like elements => a[i] is a scalar value, not a pointer
                                Type::Int | Type::UInt
                                | Type::Long | Type::ULong
                                | Type::Short | Type::UShort
                                | Type::Enum(_) | Type::Named(_)
                                | Type::Char | Type::SChar | Type::UChar => false,
                                // Non-scalar element => treat as pointer-valued (pointer to subobject)
                                _ => true,
                            }
                        }
                        _ => false,
                    }
                } else {
                    false
                }
            }
            // Cast target type is a pointer
            Expr::Cast { ty, .. } => matches!(ty, Type::Pointer(_)),
            _ => false,
        }
    }

    // ===== Helpers for multidimensional int arrays =====
    // Build LLVM type string for nested arrays whose leaf is int/uint, e.g. [2 x [3 x i32]]
    fn llvm_int_array_type_str(&self, ty: &Type) -> Option<String> {
        match ty {
            Type::Array(inner, n) => {
                let inner_str = match &**inner {
                    Type::Int | Type::UInt => Some("i32".to_string()),
                    Type::Array(_, _) => self.llvm_int_array_type_str(inner),
                    _ => None,
                }?;
                Some(format!("[{} x {}]", n, inner_str))
            }
            _ => None,
        }
    }

    // Very lightweight type inference sufficient for arrays/pointers in this backend stage
    fn type_of_expr(&self, e: &Expr) -> Option<Type> {
        match e {
            Expr::Ident(name) => self
                .locals_ty
                .get(name)
                .cloned()
                .or_else(|| self.global_types.get(name).cloned()),
            Expr::Index { base, .. } => {
                let bt = self.type_of_expr(base)?;
                match bt {
                    Type::Array(inner, _n) => Some(*inner.clone()),
                    Type::Pointer(inner) => Some(*inner.clone()),
                    _ => None,
                }
            }
            Expr::Unary {
                op: UnaryOp::AddrOf,
                expr,
            } => self.type_of_expr(expr).map(|t| Type::Pointer(Box::new(t))),
            Expr::Unary {
                op: UnaryOp::Deref,
                expr,
            } => {
                if let Some(Type::Pointer(inner)) = self.type_of_expr(expr) {
                    Some(*inner)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    // Compute pointer to element for base[index] without loading; returns (ptr_str, element_type)
    fn emit_index_ptr(&mut self, base: &Expr, index: &Expr) -> (String, Type) {
        // Fast path: if base is a plain local array identifier, use its storage pointer directly
        if let Expr::Ident(aname) = base {
            if let Some(Type::Array(inner, n)) = self.locals_ty.get(aname).cloned() {
                let (istr, ic) = self.emit_expr(index);
                let idx64 = if let Some(c) = ic {
                    format!("{}", c as i64)
                } else {
                    let z = self.new_tmp();
                    let _ = writeln!(self.buf, "  {} = zext i32 {} to i64", z, istr);
                    z
                };
                let base_ptr = self
                    .locals
                    .get(aname)
                    .cloned()
                    .unwrap_or_else(|| format!("%{}", aname));
                match *inner.clone() {
                    Type::Int | Type::UInt => {
                        let ep = self.new_tmp();
                        let _ = writeln!(
                            self.buf,
                            "  {} = getelementptr inbounds [{} x i32], ptr {}, i64 0, i64 {}",
                            ep, n, base_ptr, idx64
                        );
                        return (ep, Type::Int);
                    }
                    other => {
                        let esz = self.sizeof_t_usize(&other) as i64;
                        let scaled = if esz == 1 {
                            idx64
                        } else {
                            let m = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = mul i64 {}, {}", m, idx64, esz);
                            m
                        };
                        let ep = self.new_tmp();
                        let _ = writeln!(
                            self.buf,
                            "  {} = getelementptr inbounds i8, ptr {}, i64 {}",
                            ep, base_ptr, scaled
                        );
                        return (ep, other);
                    }
                }
            }
        }

        // Special-case struct/union member lvalues as base: compute address directly (avoid loads)
        let mut base_ty = self.type_of_expr(base);
        let bstr: String;
        if let Expr::Member { base: b2, field, arrow } = base {
            let (p, fty) = self.emit_member_ptr(b2, field, *arrow);
            bstr = p;
            base_ty = Some(fty);
        } else {
            let (p, _pc) = self.emit_expr(base);
            bstr = p;
        }

        let (istr, ic) = self.emit_expr(index);
        let idx64 = if let Some(c) = ic {
            format!("{}", c as i64)
        } else {
            let z = self.new_tmp();
            let _ = writeln!(self.buf, "  {} = zext i32 {} to i64", z, istr);
            z
        };

        match base_ty {
            Some(Type::Array(inner, _n)) => {
                // If inner is array, step rows by one: GEP typed if possible, else byte GEP
                match *inner.clone() {
                    Type::Array(_, _) => {
                        if let Some(inner_str) = self.llvm_int_array_type_str(&inner) {
                            let row = self.new_tmp();
                            let _ = writeln!(
                                self.buf,
                                "  {} = getelementptr inbounds {}, ptr {}, i64 {}",
                                row, inner_str, bstr, idx64
                            );
                            (row, *inner)
                        } else {
                            let elem_ptr = self.new_tmp();
                            let esz = self.sizeof_t_usize(&inner) as i64;
                            let scaled = if esz == 1 {
                                idx64
                            } else {
                                let m = self.new_tmp();
                                let _ = writeln!(self.buf, "  {} = mul i64 {}, {}", m, idx64, esz);
                                m
                            };
                            let _ = writeln!(
                                self.buf,
                                "  {} = getelementptr inbounds i8, ptr {}, i64 {}",
                                elem_ptr, bstr, scaled
                            );
                            (elem_ptr, *inner)
                        }
                    }
                    Type::Int | Type::UInt => {
                        let ep = self.new_tmp();
                        let _ = writeln!(
                            self.buf,
                            "  {} = getelementptr inbounds i32, ptr {}, i64 {}",
                            ep, bstr, idx64
                        );
                        (ep, Type::Int)
                    }
                    other => {
                        let elem_ptr = self.new_tmp();
                        let esz = self.sizeof_t_usize(&other) as i64;
                        let scaled = if esz == 1 {
                            idx64
                        } else {
                            let m = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = mul i64 {}, {}", m, idx64, esz);
                            m
                        };
                        let _ = writeln!(
                            self.buf,
                            "  {} = getelementptr inbounds i8, ptr {}, i64 {}",
                            elem_ptr, bstr, scaled
                        );
                        (elem_ptr, other)
                    }
                }
            }
            Some(Type::Pointer(inner)) => {
                match *inner.clone() {
                    Type::Array(_, _) => {
                        if let Some(arr_str) = self.llvm_int_array_type_str(&inner) {
                            let row = self.new_tmp();
                            let _ = writeln!(
                                self.buf,
                                "  {} = getelementptr inbounds {}, ptr {}, i64 {}",
                                row, arr_str, bstr, idx64
                            );
                            (row, *inner)
                        } else {
                            let elem_ptr = self.new_tmp();
                            let esz = self.sizeof_t_usize(&inner) as i64;
                            let scaled = if esz == 1 {
                                idx64
                            } else {
                                let m = self.new_tmp();
                                let _ = writeln!(self.buf, "  {} = mul i64 {}, {}", m, idx64, esz);
                                m
                            };
                            let _ = writeln!(
                                self.buf,
                                "  {} = getelementptr inbounds i8, ptr {}, i64 {}",
                                elem_ptr, bstr, scaled
                            );
                            (elem_ptr, *inner)
                        }
                    }
                    Type::Int | Type::UInt => {
                        let ep = self.new_tmp();
                        let _ = writeln!(
                            self.buf,
                            "  {} = getelementptr inbounds i32, ptr {}, i64 {}",
                            ep, bstr, idx64
                        );
                        (ep, Type::Int)
                    }
                    other => {
                        let elem_ptr = self.new_tmp();
                        let esz = self.sizeof_t_usize(&other) as i64;
                        let scaled = if esz == 1 {
                            idx64
                        } else {
                            let m = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = mul i64 {}, {}", m, idx64, esz);
                            m
                        };
                        let _ = writeln!(
                            self.buf,
                            "  {} = getelementptr inbounds i8, ptr {}, i64 {}",
                            elem_ptr, bstr, scaled
                        );
                        (elem_ptr, other)
                    }
                }
            }
            _ => {
                // Fallback: treat as i32 elements
                let ep = self.new_tmp();
                let _ = writeln!(
                    self.buf,
                    "  {} = getelementptr inbounds i32, ptr {}, i64 {}",
                    ep, bstr, idx64
                );
                (ep, Type::Int)
            }
        }
    }

    // Compute pointer to struct/union member; returns (ptr_to_field, field_type)
    fn emit_member_ptr(&mut self, base: &Expr, field: &str, arrow: bool) -> (String, Type) {
        // Determine base pointer and record type
        let (base_ptr, rec_ty) = if arrow {
            // base is pointer to struct/union; value is a ptr loaded from expression
            let (pv, _pc) = self.emit_expr(base);
            let rty = match base {
                Expr::Ident(n) => self
                    .locals_ty
                    .get(n)
                    .cloned()
                    .unwrap_or(Type::Pointer(Box::new(Type::Struct(String::new())))),
                _ => Type::Pointer(Box::new(Type::Struct(String::new()))),
            };
            (pv, rty)
        } else {
            // base is an lvalue (struct/union); support identifiers, nested member access, and arrays-of-structs indexing
            match base {
                Expr::Ident(n) => {
                    let ptr = self
                        .locals
                        .get(n)
                        .cloned()
                        .unwrap_or_else(|| "%0".to_string());
                    let ty = self
                        .locals_ty
                        .get(n)
                        .cloned()
                        .unwrap_or(Type::Struct(String::new()));
                    (ptr, ty)
                }
                Expr::Member {
                    base: b2,
                    field: f2,
                    arrow: a2,
                } => {
                    // Recursively compute pointer to the inner field and its type
                    let (p, fty) = self.emit_member_ptr(b2, f2, *a2);
                    (p, fty)
                }
                Expr::Index { base: arr, index } => {
                    // Handle arrays/pointers of struct/union: compute element pointer = base + idx * sizeof(elem)
                    // Try to resolve inner type when base is an identifier
                    if let Expr::Ident(aname) = &**arr {
                        if let Some(aty) = self.locals_ty.get(aname).cloned() {
                            match aty {
                                Type::Array(inner, _n) => {
                                    // Base pointer to array storage (byte buffer for non-int)
                                    let arr_ptr = self
                                        .locals
                                        .get(aname)
                                        .cloned()
                                        .unwrap_or_else(|| "%0".to_string());
                                    let esz = self.sizeof_t_usize(&inner) as i64;
                                    let (istr, ic) = self.emit_expr(index);
                                    let idx64 = if let Some(c) = ic {
                                        format!("{}", c as i64)
                                    } else {
                                        let z = self.new_tmp();
                                        let _ = writeln!(
                                            self.buf,
                                            "  {} = zext i32 {} to i64",
                                            z, istr
                                        );
                                        z
                                    };
                                    let scaled = if esz == 1 {
                                        idx64
                                    } else {
                                        let m = self.new_tmp();
                                        let _ = writeln!(
                                            self.buf,
                                            "  {} = mul i64 {}, {}",
                                            m, idx64, esz
                                        );
                                        m
                                    };
                                    let elem_ptr = self.new_tmp();
                                    let _ = writeln!(
                                        self.buf,
                                        "  {} = getelementptr inbounds i8, ptr {}, i64 {}",
                                        elem_ptr, arr_ptr, scaled
                                    );
                                    match *inner.clone() {
                                        Type::Struct(tag) => (elem_ptr, Type::Struct(tag)),
                                        Type::Union(tag) => (elem_ptr, Type::Union(tag)),
                                        _ => (elem_ptr, *inner.clone()),
                                    }
                                }
                                Type::Pointer(inner) => {
                                    // Load pointer value for p (pointer to struct/union)
                                    let (bstr, _bc) = self.emit_expr(arr);
                                    let esz = self.sizeof_t_usize(&inner) as i64;
                                    let (istr, ic) = self.emit_expr(index);
                                    let idx64 = if let Some(c) = ic {
                                        format!("{}", c as i64)
                                    } else {
                                        let z = self.new_tmp();
                                        let _ = writeln!(
                                            self.buf,
                                            "  {} = zext i32 {} to i64",
                                            z, istr
                                        );
                                        z
                                    };
                                    let scaled = if esz == 1 {
                                        idx64
                                    } else {
                                        let m = self.new_tmp();
                                        let _ = writeln!(
                                            self.buf,
                                            "  {} = mul i64 {}, {}",
                                            m, idx64, esz
                                        );
                                        m
                                    };
                                    let elem_ptr = self.new_tmp();
                                    let _ = writeln!(
                                        self.buf,
                                        "  {} = getelementptr inbounds i8, ptr {}, i64 {}",
                                        elem_ptr, bstr, scaled
                                    );
                                    match *inner.clone() {
                                        Type::Struct(tag) => (elem_ptr, Type::Struct(tag)),
                                        Type::Union(tag) => (elem_ptr, Type::Union(tag)),
                                        _ => (elem_ptr, *inner.clone()),
                                    }
                                }
                                _ => ("%0".to_string(), Type::Struct(String::new())),
                            }
                        } else {
                            ("%0".to_string(), Type::Struct(String::new()))
                        }
                    } else {
                        // Fallback: compute base pointer and assume element size 1 (byte) if unknown
                        let (bstr, _bc) = self.emit_expr(arr);
                        let (istr, ic) = self.emit_expr(index);
                        let idx64 = if let Some(c) = ic {
                            format!("{}", c as i64)
                        } else {
                            let z = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = zext i32 {} to i64", z, istr);
                            z
                        };
                        let elem_ptr = self.new_tmp();
                        let _ = writeln!(
                            self.buf,
                            "  {} = getelementptr inbounds i8, ptr {}, i64 {}",
                            elem_ptr, bstr, idx64
                        );
                        (elem_ptr, Type::Struct(String::new()))
                    }
                }
                _ => ("%0".to_string(), Type::Struct(String::new())),
            }
        };

        match rec_ty {
            Type::Struct(tag) => {
                // Prefetch (offset, type) to avoid overlapping immutable/mutable borrows
                let (off_opt, fty_opt) = {
                    if let Some(sl) = self.struct_layouts.get(&tag) {
                        if let Some((off, fty)) = sl.members.get(field) {
                            (Some(*off), Some(fty.clone()))
                        } else {
                            (None, None)
                        }
                    } else {
                        (None, None)
                    }
                };
                if let (Some(off), Some(fty)) = (off_opt, fty_opt) {
                    let gep = self.new_tmp();
                    let _ = writeln!(
                        self.buf,
                        "  {} = getelementptr inbounds i8, ptr {}, i64 {}",
                        gep, base_ptr, off as i64
                    );
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
                            } else {
                                (None, None)
                            }
                        } else {
                            (None, None)
                        }
                    };
                    if let (Some(off), Some(fty)) = (off_opt, fty_opt) {
                        let gep = self.new_tmp();
                        let _ = writeln!(
                            self.buf,
                            "  {} = getelementptr inbounds i8, ptr {}, i64 {}",
                            gep, base_ptr, off as i64
                        );
                        return (gep, fty);
                    }
                    (base_ptr, Type::Int)
                }
                Type::Union(ref tag) => {
                    let fty_opt = {
                        if let Some(ul) = self.union_layouts.get(tag) {
                            ul.members.get(field).cloned()
                        } else {
                            None
                        }
                    };
                    if let Some(fty) = fty_opt {
                        let gep = self.new_tmp();
                        let _ = writeln!(
                            self.buf,
                            "  {} = getelementptr inbounds i8, ptr {}, i64 0",
                            gep, base_ptr
                        );
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
                    } else {
                        None
                    }
                };
                if let Some(fty) = fty_opt {
                    let gep = self.new_tmp();
                    let _ = writeln!(
                        self.buf,
                        "  {} = getelementptr inbounds i8, ptr {}, i64 0",
                        gep, base_ptr
                    );
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
                // Prefer local variables first
                if let Some(ptr) = self.locals.get(name).cloned() {
                    // Snapshot type to avoid immutable + mutable borrow overlap
                    let lty = self.locals_ty.get(name).cloned();
                    match lty {
                        // Load all integer-like kinds as i32
                        Some(Type::Char) | Some(Type::SChar) | Some(Type::UChar)
                        | Some(Type::Short) | Some(Type::UShort) | Some(Type::Int)
                        | Some(Type::UInt) | Some(Type::Long) | Some(Type::ULong)
                        | Some(Type::Enum(_)) | Some(Type::Named(_)) => {
                            let tmp = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = load i32, ptr {}", tmp, ptr);
                            let c = if self.in_loop == 0 {
                                self.consts.get(name).copied()
                            } else {
                                None
                            };
                            if let Some(v) = c {
                                (format!("{}", v), c)
                            } else {
                                (tmp, None)
                            }
                        }
                        Some(Type::Pointer(_)) => {
                            let tmp = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = load ptr, ptr {}", tmp, ptr);
                            (tmp, None)
                        }
                        Some(Type::Array(inner, n)) => {
                            // Decay to pointer to first element. For nested arrays of int, keep correct element type.
                            if let Some(full_arr) =
                                self.llvm_int_array_type_str(&Type::Array(inner.clone(), n))
                            {
                                let dec = self.new_tmp();
                                let _ = writeln!(
                                    self.buf,
                                    "  {} = getelementptr inbounds {}, ptr {}, i64 0, i64 0",
                                    dec, full_arr, ptr
                                );
                                (dec, None)
                            } else {
                                // For non-int element arrays: return base storage pointer (i8 buffer)
                                (ptr, None)
                            }
                        }
                        // Struct/union as rvalue not supported -> return 0 for now
                        Some(Type::Struct(_)) | Some(Type::Union(_)) => ("0".to_string(), Some(0)),
                        _ => ("0".to_string(), Some(0)),
                    }
                } else if let Some(gty) = self.global_types.get(name).cloned() {
                    match gty {
                        // Load all integer-like kinds as i32
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
                        | Type::Named(_) => {
                            let tmp = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = load i32, ptr @{}", tmp, name);
                            (tmp, None)
                        }
                        Type::Pointer(_) => {
                            let tmp = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = load ptr, ptr @{}", tmp, name);
                            (tmp, None)
                        }
                        Type::Array(inner, n) => {
                            if let Some(full_arr) =
                                self.llvm_int_array_type_str(&Type::Array(inner.clone(), n))
                            {
                                let dec = self.new_tmp();
                                let _ = writeln!(
                                    self.buf,
                                    "  {} = getelementptr inbounds {}, ptr @{}, i64 0, i64 0",
                                    dec, full_arr, name
                                );
                                (dec, None)
                            } else {
                                (format!("@{}", name), None)
                            }
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
                            None => {
                                let tmp = self.new_tmp();
                                let _ = writeln!(self.buf, "  {} = sub i32 0, {}", tmp, vstr);
                                (tmp, None)
                            }
                        }
                    }
                    UnaryOp::BitNot => {
                        let (vstr, vc) = self.emit_expr(expr);
                        match vc {
                            Some(c) => (format!("{}", !c), Some(!c)),
                            None => {
                                let tmp = self.new_tmp();
                                let _ = writeln!(self.buf, "  {} = xor i32 {}, -1", tmp, vstr);
                                (tmp, None)
                            }
                        }
                    }
                    UnaryOp::LogicalNot => {
                        let (vstr, vc) = self.emit_expr(expr);
                        match vc {
                            Some(c) => (
                                format!("{}", if c == 0 { 1 } else { 0 }),
                                Some(if c == 0 { 1 } else { 0 }),
                            ),
                            None => {
                                let cmp = self.new_tmp();
                                let _ = writeln!(self.buf, "  {} = icmp eq i32 {}, 0", cmp, vstr);
                                let z = self.new_tmp();
                                let _ = writeln!(self.buf, "  {} = zext i1 {} to i32", z, cmp);
                                (z, None)
                            }
                        }
                    }
                    UnaryOp::AddrOf => {
                        match &**expr {
                            Expr::Ident(name) => {
                                if let Some(ptr) = self.locals.get(name).cloned() {
                                    (ptr, None)
                                } else if self.global_types.contains_key(name) {
                                    // Known global/function symbol
                                    (format!("@{}", name), None)
                                } else {
                                    // Assume function symbol if not a local or known global
                                    (format!("@{}", name), None)
                                }
                            }
                            Expr::Member { base, field, arrow } => {
                                let (p, _fty) = self.emit_member_ptr(base, field, *arrow);
                                (p, None)
                            }
                            Expr::Index { base, index } => {
                                let (p, _ety) = self.emit_index_ptr(base, index);
                                (p, None)
                            }
                            _ => ("0".to_string(), Some(0)),
                        }
                    }
                    UnaryOp::Deref => {
                        // Special-case *(&func) -> @func (no load)
                        if let Expr::Unary {
                            op: UnaryOp::AddrOf,
                            expr: inner,
                        } = &**expr
                        {
                            if let Expr::Ident(name) = &**inner {
                                (format!("@{}", name), None)
                            } else {
                                let (pstr, _pc) = self.emit_expr(expr);
                                let tmp = self.new_tmp();
                                let _ = writeln!(self.buf, "  {} = load i32, ptr {}", tmp, pstr);
                                (tmp, None)
                            }
                        } else {
                            let (pstr, _pc) = self.emit_expr(expr);
                            let tmp = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = load i32, ptr {}", tmp, pstr);
                            (tmp, None)
                        }
                    }
                }
            }

            Expr::Binary { op, lhs, rhs } => {
                // Pointer arithmetic via GEP when mixing ptr and int for +/-
                if matches!(op, BinaryOp::Plus | BinaryOp::Minus) {
                    let lhs_is_ptr = self.expr_is_pointer(lhs);
                    let rhs_is_ptr = self.expr_is_pointer(rhs);
                    if lhs_is_ptr && !rhs_is_ptr {
                        let (lv_str, _lv_c) = self.emit_expr(lhs);
                        let (rv_str, rv_c) = self.emit_expr(rhs);
                        // Build i64 index with sign for minus
                        // Build i64 index: dynamic (non-literal) path uses zext and optional negate for minus
                        let idx64 = if matches!(&**rhs, Expr::IntLiteral(_)) {
                            // Allow constant immediates to fold directly
                            if let Some(c) = rv_c {
                                let v: i64 = if matches!(op, BinaryOp::Minus) { -(c as i64) } else { c as i64 };
                                format!("{}", v)
                            } else {
                                let z = self.new_tmp();
                                let _ = writeln!(self.buf, "  {} = zext i32 {} to i64", z, rv_str);
                                if matches!(op, BinaryOp::Minus) {
                                    let neg = self.new_tmp();
                                    let _ = writeln!(self.buf, "  {} = sub i64 0, {}", neg, z);
                                    neg
                                } else {
                                    z
                                }
                            }
                        } else {
                            let z = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = zext i32 {} to i64", z, rv_str);
                            if matches!(op, BinaryOp::Minus) {
                                let neg = self.new_tmp();
                                let _ = writeln!(self.buf, "  {} = sub i64 0, {}", neg, z);
                                neg
                            } else {
                                z
                            }
                        };
                        // Determine element size from pointer type
                        let (elem_sz, is_i32_elem) = match self.type_of_expr(lhs) {
                            Some(Type::Pointer(inner)) => {
                                let sz = self.sizeof_t_usize(&inner) as i64;
                                let is_i32 = matches!(*inner, Type::Int | Type::UInt);
                                (if sz == 0 { 4 } else { sz }, is_i32)
                            }
                            _ => (4, true),
                        };
                        if is_i32_elem {
                            // Use typed GEP for i32 elements
                            let gep = self.new_tmp();
                            let _ = writeln!(
                                self.buf,
                                "  {} = getelementptr inbounds i32, ptr {}, i64 {}",
                                gep, lv_str, idx64
                            );
                            return (gep, None);
                        } else {
                            // Byte GEP scaled by element size
                            let scaled = if elem_sz == 1 {
                                idx64
                            } else {
                                let m = self.new_tmp();
                                let _ = writeln!(self.buf, "  {} = mul i64 {}, {}", m, idx64, elem_sz);
                                m
                            };
                            let gep = self.new_tmp();
                            let _ = writeln!(
                                self.buf,
                                "  {} = getelementptr inbounds i8, ptr {}, i64 {}",
                                gep, lv_str, scaled
                            );
                            return (gep, None);
                        }
                    } else if !lhs_is_ptr && rhs_is_ptr && matches!(op, BinaryOp::Plus) {
                        let (lv_str, lv_c) = self.emit_expr(lhs);
                        let (rv_str, _rv_c) = self.emit_expr(rhs);
                        let idx64 = if let Some(c) = lv_c {
                            format!("{}", c as i64)
                        } else {
                            let z = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = zext i32 {} to i64", z, lv_str);
                            z
                        };
                        let (elem_sz, is_i32_elem) = match self.type_of_expr(rhs) {
                            Some(Type::Pointer(inner)) => {
                                let sz = self.sizeof_t_usize(&inner) as i64;
                                let is_i32 = matches!(*inner, Type::Int | Type::UInt);
                                (if sz == 0 { 4 } else { sz }, is_i32)
                            }
                            _ => (4, true),
                        };
                        if is_i32_elem {
                            let gep = self.new_tmp();
                            let _ = writeln!(
                                self.buf,
                                "  {} = getelementptr inbounds i32, ptr {}, i64 {}",
                                gep, rv_str, idx64
                            );
                            return (gep, None);
                        } else {
                            let scaled = if elem_sz == 1 {
                                idx64
                            } else {
                                let m = self.new_tmp();
                                let _ = writeln!(self.buf, "  {} = mul i64 {}, {}", m, idx64, elem_sz);
                                m
                            };
                            let gep = self.new_tmp();
                            let _ = writeln!(
                                self.buf,
                                "  {} = getelementptr inbounds i8, ptr {}, i64 {}",
                                gep, rv_str, scaled
                            );
                            return (gep, None);
                        }
                    }
                }
                // Pointer subtraction: ptr - ptr => element difference (i32)
                if matches!(op, BinaryOp::Minus) {
                    let lhs_is_ptr = self.expr_is_pointer(lhs);
                    let rhs_is_ptr = self.expr_is_pointer(rhs);
                    if lhs_is_ptr && rhs_is_ptr {
                        let (lv_str, _lv_c) = self.emit_expr(lhs);
                        let (rv_str, _rv_c) = self.emit_expr(rhs);
                        let li64 = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = ptrtoint ptr {} to i64", li64, lv_str);
                        let ri64 = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = ptrtoint ptr {} to i64", ri64, rv_str);
                        let diff = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = sub i64 {}, {}", diff, li64, ri64);
                        // Determine element size (default 4 for int)
                        let elem_sz = match self.type_of_expr(lhs) {
                            Some(Type::Pointer(inner)) => self.sizeof_t_usize(&inner) as i64,
                            _ => 4,
                        };
                        let elems = if elem_sz == 1 {
                            diff.clone()
                        } else {
                            let d = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = sdiv i64 {}, {}", d, diff, elem_sz);
                            d
                        };
                        let out = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = trunc i64 {} to i32", out, elems);
                        return (out, None);
                    }
                }

                // Unsigned-aware integer arithmetic selection
                let lhs_uint = match &**lhs {
                    Expr::Ident(n) => {
                        matches!(
                            self.locals_ty.get(n),
                            Some(Type::UChar)
                                | Some(Type::UShort)
                                | Some(Type::UInt)
                                | Some(Type::ULong)
                        ) || matches!(
                            self.global_types.get(n),
                            Some(Type::UChar)
                                | Some(Type::UShort)
                                | Some(Type::UInt)
                                | Some(Type::ULong)
                        )
                    }
                    Expr::Cast { ty, .. } => {
                        matches!(ty, Type::UChar | Type::UShort | Type::UInt | Type::ULong)
                    }
                    _ => false,
                };
                let rhs_uint = match &**rhs {
                    Expr::Ident(n) => {
                        matches!(
                            self.locals_ty.get(n),
                            Some(Type::UChar)
                                | Some(Type::UShort)
                                | Some(Type::UInt)
                                | Some(Type::ULong)
                        ) || matches!(
                            self.global_types.get(n),
                            Some(Type::UChar)
                                | Some(Type::UShort)
                                | Some(Type::UInt)
                                | Some(Type::ULong)
                        )
                    }
                    Expr::Cast { ty, .. } => {
                        matches!(ty, Type::UChar | Type::UShort | Type::UInt | Type::ULong)
                    }
                    _ => false,
                };
                let unsigned = lhs_uint || rhs_uint;

                // Default integer arithmetic
                let (lv_str, lv_c) = self.emit_expr(lhs);
                let (rv_str, rv_c) = self.emit_expr(rhs);

                // Minimal constant folding: handle literal addition to enable constant propagation
                if let (Some(la), Some(rb)) = (lv_c, rv_c) {
                    if matches!(op, BinaryOp::Plus) {
                        let v = la.wrapping_add(rb);
                        return (format!("{}", v), Some(v));
                    }
                }

                // Special-case: fold sizeof(...) - sizeof(...) into a literal constant
                if matches!(op, BinaryOp::Minus) {
                    let lhs_is_sizeof = matches!(&**lhs, Expr::SizeofType(_) | Expr::SizeofExpr(_));
                    let rhs_is_sizeof = matches!(&**rhs, Expr::SizeofType(_) | Expr::SizeofExpr(_));
                    if lhs_is_sizeof && rhs_is_sizeof {
                        if let (Some(la), Some(rb)) = (lv_c, rv_c) {
                            let v = la.wrapping_sub(rb);
                            return (format!("{}", v), Some(v));
                        }
                    }
                }

                match op {
                    // Arithmetic and bitwise (with unsigned-aware div/mod and shift handling)
                    BinaryOp::Plus => {
                        self.bin_arith("add", lv_str, rv_str, lv_c, rv_c, |a, b| a.wrapping_add(b))
                    }
                    BinaryOp::Minus => {
                        self.bin_arith("sub", lv_str, rv_str, lv_c, rv_c, |a, b| a.wrapping_sub(b))
                    }
                    BinaryOp::Mul => {
                        self.bin_arith("mul", lv_str, rv_str, lv_c, rv_c, |a, b| a.wrapping_mul(b))
                    }
                    BinaryOp::Div => {
                        let op_str = if unsigned { "udiv" } else { "sdiv" };
                        self.bin_arith(op_str, lv_str, rv_str, lv_c, rv_c, |a, b| {
                            if b != 0 {
                                a.wrapping_div(b)
                            } else {
                                0
                            }
                        })
                    }
                    BinaryOp::Mod => {
                        let op_str = if unsigned { "urem" } else { "srem" };
                        self.bin_arith(op_str, lv_str, rv_str, lv_c, rv_c, |a, b| {
                            if b != 0 {
                                a.wrapping_rem(b)
                            } else {
                                0
                            }
                        })
                    }
                    BinaryOp::Shl => self.bin_arith("shl", lv_str, rv_str, lv_c, rv_c, |a, b| {
                        a.wrapping_shl((b as u32) & 31)
                    }),
                    BinaryOp::Shr => {
                        let shr_op = if lhs_uint { "lshr" } else { "ashr" };
                        self.bin_arith(shr_op, lv_str, rv_str, lv_c, rv_c, |a, b| {
                            a >> ((b as u32) & 31)
                        })
                    }
                    BinaryOp::BitAnd => {
                        self.bin_arith("and", lv_str, rv_str, lv_c, rv_c, |a, b| a & b)
                    }
                    BinaryOp::BitOr => {
                        self.bin_arith("or", lv_str, rv_str, lv_c, rv_c, |a, b| a | b)
                    }
                    BinaryOp::BitXor => {
                        self.bin_arith("xor", lv_str, rv_str, lv_c, rv_c, |a, b| a ^ b)
                    }

                    // Logical with i1 and zext to i32 (no short-circuit side effects for now)
                    BinaryOp::LAnd | BinaryOp::LOr => {
                        let (lb_str, lb_c) = self.to_bool(lv_str, lv_c);
                        let (rb_str, rb_c) = self.to_bool(rv_str, rv_c);
                        if let (Some(la), Some(rb)) = (lb_c, rb_c) {
                            let v = match op {
                                BinaryOp::LAnd => (la && rb) as i32,
                                BinaryOp::LOr => (la || rb) as i32,
                                _ => 0,
                            };
                            (format!("{}", v), Some(v))
                        } else {
                            let tmpb = self.new_tmp();
                            match (lb_c, rb_c) {
                                (Some(la), None) => {
                                    let _ = writeln!(
                                        self.buf,
                                        "  {} = {} i1 {}, {}",
                                        tmpb,
                                        if matches!(op, BinaryOp::LAnd) {
                                            "and"
                                        } else {
                                            "or"
                                        },
                                        if la { "true" } else { "false" },
                                        rb_str
                                    );
                                }
                                (None, Some(rbv)) => {
                                    let _ = writeln!(
                                        self.buf,
                                        "  {} = {} i1 {}, {}",
                                        tmpb,
                                        if matches!(op, BinaryOp::LAnd) {
                                            "and"
                                        } else {
                                            "or"
                                        },
                                        lb_str,
                                        if rbv { "true" } else { "false" }
                                    );
                                }
                                (None, None) => {
                                    let _ = writeln!(
                                        self.buf,
                                        "  {} = {} i1 {}, {}",
                                        tmpb,
                                        if matches!(op, BinaryOp::LAnd) {
                                            "and"
                                        } else {
                                            "or"
                                        },
                                        lb_str,
                                        rb_str
                                    );
                                }
                                (Some(_), Some(_)) => unreachable!(),
                            }
                            let z = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = zext i1 {} to i32", z, tmpb);
                            (z, None)
                        }
                    }

                    // Comparisons -> icmp + zext to i32 (unsigned predicates if either operand unsigned)
                    BinaryOp::Lt
                    | BinaryOp::Le
                    | BinaryOp::Gt
                    | BinaryOp::Ge
                    | BinaryOp::Eq
                    | BinaryOp::Ne => {
                        // Pointer-aware comparisons: if either operand is a pointer, compare as ptr
                        let l_is_ptr = self.expr_is_pointer(lhs);
                        let r_is_ptr = self.expr_is_pointer(rhs);
                        if l_is_ptr || r_is_ptr {
                            // We already have lv_str/rv_str as the evaluated values; convert ints to ptr if needed
                            let lp = if l_is_ptr {
                                lv_str.clone()
                            } else {
                                let t = self.new_tmp();
                                let _ = writeln!(self.buf, "  {} = inttoptr i32 {} to ptr", t, lv_str);
                                t
                            };
                            let rp = if r_is_ptr {
                                rv_str.clone()
                            } else {
                                let t = self.new_tmp();
                                let _ = writeln!(self.buf, "  {} = inttoptr i32 {} to ptr", t, rv_str);
                                t
                            };
                            // Use unsigned predicates for ordering; eq/ne are fine
                            let pred = match op {
                                BinaryOp::Lt => "ult",
                                BinaryOp::Le => "ule",
                                BinaryOp::Gt => "ugt",
                                BinaryOp::Ge => "uge",
                                BinaryOp::Eq => "eq",
                                BinaryOp::Ne => "ne",
                                _ => unreachable!(),
                            };
                            let ctmp = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = icmp {} ptr {}, {}", ctmp, pred, lp, rp);
                            let z = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = zext i1 {} to i32", z, ctmp);
                            return (z, None);
                        }

                        let pred = match op {
                            BinaryOp::Lt => {
                                if unsigned {
                                    "ult"
                                } else {
                                    "slt"
                                }
                            }
                            BinaryOp::Le => {
                                if unsigned {
                                    "ule"
                                } else {
                                    "sle"
                                }
                            }
                            BinaryOp::Gt => {
                                if unsigned {
                                    "ugt"
                                } else {
                                    "sgt"
                                }
                            }
                            BinaryOp::Ge => {
                                if unsigned {
                                    "uge"
                                } else {
                                    "sge"
                                }
                            }
                            BinaryOp::Eq => "eq",
                            BinaryOp::Ne => "ne",
                            _ => unreachable!(),
                        };
                        let ctmp = self.new_tmp();
                        let _ = writeln!(
                            self.buf,
                            "  {} = icmp {} i32 {}, {}",
                            ctmp, pred, lv_str, rv_str
                        );
                        let z = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = zext i1 {} to i32", z, ctmp);
                        (z, None)
                    }
                }
            },
            // Array indexing with nested arrays: compute pointer with emit_index_ptr and load only for int element
            Expr::Index { base, index } => {
                let (eptr, ety) = self.emit_index_ptr(base, index);
                match ety {
                    Type::Int | Type::UInt => {
                        let val = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = load i32, ptr {}", val, eptr);
                        (val, None)
                    }
                    _ => (eptr, None),
                }
            }
            // Casts: handle int<->ptr and ptr->ptr (fallback for other types)
            Expr::Cast { ty, expr } => {
                let (vstr, vc) = self.emit_expr(expr);
                match ty {
                    Type::Int | Type::UInt => {
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
                            // int -> ptr
                            let tmp = self.new_tmp();
                            let _ = writeln!(self.buf, "  {} = inttoptr i32 {} to ptr", tmp, vstr);
                            (tmp, None)
                        }
                    }
                    _ => {
                        // Fallback: leave value as-is
                        (vstr, vc)
                    }
                }
            }
            // Function calls: puts (special), printf (varargs), generic
            Expr::Call { callee, args } => {
                if callee == "puts" && args.len() == 1 {
                    self.add_decl("declare i32 @puts(ptr)");
                    let mut arg_strs: Vec<String> = Vec::new();
                    match &args[0] {
                        Expr::StringLiteral(repr) => {
                            let p = self.emit_string_ptr(repr);
                            arg_strs.push(format!("ptr {}", p));
                        }
                        other => {
                            let (v, _c) = self.emit_expr(other);
                            if self.expr_is_pointer(other) {
                                arg_strs.push(format!("ptr {}", v));
                            } else {
                                // Fallback: int -> ptr for non-string arg
                                let t = self.new_tmp();
                                let _ = writeln!(self.buf, "  {} = inttoptr i32 {} to ptr", t, v);
                                arg_strs.push(format!("ptr {}", t));
                            }
                        }
                    }
                    let tmp = self.new_tmp();
                    let _ = write!(self.buf, "  {} = call i32 @{}(", tmp, callee);
                    for (i, a) in arg_strs.iter().enumerate() {
                        let _ = write!(
                            self.buf,
                            "{}{}",
                            a,
                            if i + 1 < arg_strs.len() { ", " } else { "" }
                        );
                    }
                    let _ = writeln!(self.buf, ")");
                    (tmp, None)
                } else if callee == "printf" {
                    // Varargs printf: declare once and type arguments (ptr for format, i32 for ints, ptr for pointers)
                    self.add_decl("declare i32 @printf(ptr, ...)");
                    let mut parts: Vec<String> = Vec::new();
                    for (i, a) in args.iter().enumerate() {
                        if i == 0 {
                            // First argument must be a pointer (format string)
                            match a {
                                Expr::StringLiteral(repr) => {
                                    let p = self.emit_string_ptr(repr);
                                    parts.push(format!("ptr {}", p));
                                }
                                _ => {
                                    let (v, _c) = self.emit_expr(a);
                                    if self.expr_is_pointer(a) {
                                        parts.push(format!("ptr {}", v));
                                    } else {
                                        // Fallback: int -> ptr for non-string first arg
                                        let t = self.new_tmp();
                                        let _ = writeln!(
                                            self.buf,
                                            "  {} = inttoptr i32 {} to ptr",
                                            t, v
                                        );
                                        parts.push(format!("ptr {}", t));
                                    }
                                }
                            }
                        } else {
                            // Subsequent arguments: i32 for integers; ptr for pointers
                            if self.expr_is_pointer(a) {
                                let (v, _c) = self.emit_expr(a);
                                parts.push(format!("ptr {}", v));
                            } else {
                                let (v, _c) = self.emit_expr(a);
                                parts.push(format!("i32 {}", v));
                            }
                        }
                    }
                    let tmp = self.new_tmp();
                    let _ = write!(self.buf, "  {} = call i32 @printf(", tmp);
                    for (i, p) in parts.iter().enumerate() {
                        let _ = write!(
                            self.buf,
                            "{}{}",
                            p,
                            if i + 1 < parts.len() { ", " } else { "" }
                        );
                    }
                    let _ = writeln!(self.buf, ")");
                    (tmp, None)
                } else {
                    let mut arg_vals: Vec<String> = Vec::new();
                    for a in args {
                        let (s, _c) = self.emit_expr(a);
                        arg_vals.push(s);
                    }
                    // Ensure external declaration for callee only if not already defined in this module
                    let already_defined = self.buf.contains(&format!("define i32 @{}(", callee));
                    if !already_defined {
                        let mut decl = format!("declare i32 @{}(", callee);
                        for i in 0..arg_vals.len() {
                            if i > 0 {
                                decl.push_str(", ");
                            }
                            decl.push_str("i32");
                        }
                        decl.push(')');
                        self.add_decl(&decl);
                    }
                    let tmp = self.new_tmp();
                    let _ = write!(self.buf, "  {} = call i32 @{}(", tmp, callee);
                    for (i, av) in arg_vals.iter().enumerate() {
                        let _ = write!(
                            self.buf,
                            "i32 {}{}",
                            av,
                            if i + 1 < arg_vals.len() { ", " } else { "" }
                        );
                    }
                    let _ = writeln!(self.buf, ")");
                    (tmp, None)
                }
            }
            // Indirect call via function pointer
            Expr::CallPtr { target, args } => {
                let (tstr, _tc) = self.emit_expr(target);
                // Build argument list: i32 for ints, ptr for pointers (as per our current convention)
                let mut parts: Vec<String> = Vec::new();
                for a in args {
                    if self.expr_is_pointer(a) {
                        let (v, _c) = self.emit_expr(a);
                        parts.push(format!("ptr {}", v));
                    } else {
                        let (v, _c) = self.emit_expr(a);
                        parts.push(format!("i32 {}", v));
                    }
                }
                let tmp = self.new_tmp();
                let _ = write!(self.buf, "  {} = call i32 {}(", tmp, tstr);
                for (i, p) in parts.iter().enumerate() {
                    let _ = write!(
                        self.buf,
                        "{}{}",
                        p,
                        if i + 1 < parts.len() { ", " } else { "" }
                    );
                }
                let _ = writeln!(self.buf, ")");
                (tmp, None)
            }
            // Ternary/conditional expression: cond ? then_e : else_e (emit control-flow with join)
            Expr::Cond {
                cond,
                then_e,
                else_e,
            } => {
                // Evaluate condition to i1
                let (cv_str, cv_c) = self.emit_expr(cond);
                let (c_i1, _c_b) = self.to_bool(cv_str, cv_c);

                // Determine result kind (ptr vs i32) ahead of time and allocate a slot
                let t_is_ptr = self.expr_is_pointer(then_e);
                let e_is_ptr = self.expr_is_pointer(else_e);
                let res_is_ptr = t_is_ptr || e_is_ptr;
                let res_slot = self.new_tmp();
                if res_is_ptr {
                    let _ = writeln!(self.buf, "  {} = alloca ptr", res_slot);
                } else {
                    let _ = writeln!(self.buf, "  {} = alloca i32", res_slot);
                }

                // Create blocks
                let then_lbl = self.new_label();
                let else_lbl = self.new_label();
                let join_lbl = self.new_label();

                // Branch on condition
                self.br_cond(&c_i1, &then_lbl, &else_lbl);

                // Then block
                self.start_block(&then_lbl);
                let (tv_str, _tc) = self.emit_expr(then_e);
                if res_is_ptr {
                    let tval = if t_is_ptr {
                        tv_str.clone()
                    } else {
                        let t = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = inttoptr i32 {} to ptr", t, tv_str);
                        t
                    };
                    let _ = writeln!(self.buf, "  store ptr {}, ptr {}", tval, res_slot);
                } else {
                    let tval = if t_is_ptr {
                        let t = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = ptrtoint ptr {} to i32", t, tv_str);
                        t
                    } else {
                        tv_str.clone()
                    };
                    let _ = writeln!(self.buf, "  store i32 {}, ptr {}", tval, res_slot);
                }
                self.br_uncond(&join_lbl);

                // Else block
                self.start_block(&else_lbl);
                let (ev_str, _ec) = self.emit_expr(else_e);
                if res_is_ptr {
                    let evalv = if e_is_ptr {
                        ev_str.clone()
                    } else {
                        let t = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = inttoptr i32 {} to ptr", t, ev_str);
                        t
                    };
                    let _ = writeln!(self.buf, "  store ptr {}, ptr {}", evalv, res_slot);
                } else {
                    let evalv = if e_is_ptr {
                        let t = self.new_tmp();
                        let _ = writeln!(self.buf, "  {} = ptrtoint ptr {} to i32", t, ev_str);
                        t
                    } else {
                        ev_str.clone()
                    };
                    let _ = writeln!(self.buf, "  store i32 {}, ptr {}", evalv, res_slot);
                }
                self.br_uncond(&join_lbl);

                // Join block: load and return the result SSA
                self.start_block(&join_lbl);
                if res_is_ptr {
                    let res = self.new_tmp();
                    let _ = writeln!(self.buf, "  {} = load ptr, ptr {}", res, res_slot);
                    (res, None)
                } else {
                    let res = self.new_tmp();
                    let _ = writeln!(self.buf, "  {} = load i32, ptr {}", res, res_slot);
                    (res, None)
                }
            }
            Expr::IncDec { pre, inc, target } => match &**target {
                Expr::Ident(name) => {
                    let ptr = if let Some(p) = self.locals.get(name) {
                        p.clone()
                    } else {
                        let p = format!("%{}.addr", name);
                        let _ = writeln!(self.buf, "  {} = alloca i32", p);
                        self.locals.insert(name.clone(), p.clone());
                        self.locals_ty.insert(name.clone(), Type::Int);
                        p
                    };
                    let old = self.new_tmp();
                    let _ = writeln!(self.buf, "  {} = load i32, ptr {}", old, ptr);
                    let (newv, _c) = if *inc {
                        self.bin_arith(
                            "add",
                            old.clone(),
                            "1".to_string(),
                            None,
                            Some(1),
                            |a, b| a.wrapping_add(b),
                        )
                    } else {
                        self.bin_arith(
                            "sub",
                            old.clone(),
                            "1".to_string(),
                            None,
                            Some(1),
                            |a, b| a.wrapping_sub(b),
                        )
                    };
                    let _ = writeln!(self.buf, "  store i32 {}, ptr {}", newv, ptr);
                    self.consts.remove(name);
                    if *pre {
                        (newv, None)
                    } else {
                        (old, None)
                    }
                }
                Expr::Unary {
                    op: UnaryOp::Deref,
                    expr: pexpr,
                } => {
                    let (pstr, _pc) = self.emit_expr(pexpr);
                    let old = self.new_tmp();
                    let _ = writeln!(self.buf, "  {} = load i32, ptr {}", old, pstr);
                    let (newv, _c) = if *inc {
                        self.bin_arith(
                            "add",
                            old.clone(),
                            "1".to_string(),
                            None,
                            Some(1),
                            |a, b| a.wrapping_add(b),
                        )
                    } else {
                        self.bin_arith(
                            "sub",
                            old.clone(),
                            "1".to_string(),
                            None,
                            Some(1),
                            |a, b| a.wrapping_sub(b),
                        )
                    };
                    let _ = writeln!(self.buf, "  store i32 {}, ptr {}", newv, pstr);
                    self.consts.clear();
                    if *pre {
                        (newv, None)
                    } else {
                        (old, None)
                    }
                }
                _ => {
                    let (v, _c) = self.emit_expr(target);
                    (v, None)
                }
            },
            // Compound assignment: lhs op= rhs
            Expr::AssignOp { op, lhs, rhs } => match &**lhs {
                Expr::Ident(name) => {
                    let ptr = if let Some(p) = self.locals.get(name) {
                        p.clone()
                    } else {
                        let p = format!("%{}.addr", name);
                        let _ = writeln!(self.buf, "  {} = alloca i32", p);
                        self.locals.insert(name.clone(), p.clone());
                        self.locals_ty.insert(name.clone(), Type::Int);
                        p
                    };
                    let ltmp = self.new_tmp();
                    let _ = writeln!(self.buf, "  {} = load i32, ptr {}", ltmp, ptr);
                    let (rv_str, rv_c) = self.emit_expr(rhs);
                    let (res_str, res_c) = match op {
                        BinaryOp::Plus => {
                            self.bin_arith("add", ltmp.clone(), rv_str, None, rv_c, |a, b| {
                                a.wrapping_add(b)
                            })
                        }
                        BinaryOp::Minus => {
                            self.bin_arith("sub", ltmp.clone(), rv_str, None, rv_c, |a, b| {
                                a.wrapping_sub(b)
                            })
                        }
                        BinaryOp::Mul => {
                            self.bin_arith("mul", ltmp.clone(), rv_str, None, rv_c, |a, b| {
                                a.wrapping_mul(b)
                            })
                        }
                        BinaryOp::Div => {
                            self.bin_arith("sdiv", ltmp.clone(), rv_str, None, rv_c, |a, b| {
                                if b != 0 {
                                    a.wrapping_div(b)
                                } else {
                                    0
                                }
                            })
                        }
                        BinaryOp::Mod => {
                            self.bin_arith("srem", ltmp.clone(), rv_str, None, rv_c, |a, b| {
                                if b != 0 {
                                    a.wrapping_rem(b)
                                } else {
                                    0
                                }
                            })
                        }
                        BinaryOp::Shl => {
                            self.bin_arith("shl", ltmp.clone(), rv_str, None, rv_c, |a, b| {
                                a.wrapping_shl((b as u32) & 31)
                            })
                        }
                        BinaryOp::Shr => {
                            self.bin_arith("ashr", ltmp.clone(), rv_str, None, rv_c, |a, b| {
                                (a >> ((b as u32) & 31))
                            })
                        }
                        BinaryOp::BitAnd => {
                            self.bin_arith("and", ltmp.clone(), rv_str, None, rv_c, |a, b| a & b)
                        }
                        BinaryOp::BitOr => {
                            self.bin_arith("or", ltmp.clone(), rv_str, None, rv_c, |a, b| a | b)
                        }
                        BinaryOp::BitXor => {
                            self.bin_arith("xor", ltmp.clone(), rv_str, None, rv_c, |a, b| a ^ b)
                        }
                        _ => (ltmp.clone(), None),
                    };
                    let _ = writeln!(self.buf, "  store i32 {}, ptr {}", res_str, ptr);
                    if let Some(c) = res_c {
                        self.consts.insert(name.clone(), c);
                    } else {
                        self.consts.remove(name);
                    }
                    (res_str, res_c)
                }
                Expr::Unary {
                    op: UnaryOp::Deref,
                    expr: pexpr,
                } => {
                    let (pstr, _pc) = self.emit_expr(pexpr);
                    let ltmp = self.new_tmp();
                    let _ = writeln!(self.buf, "  {} = load i32, ptr {}", ltmp, pstr);
                    let (rv_str, rv_c) = self.emit_expr(rhs);
                    let (res_str, _res_c) = match op {
                        BinaryOp::Plus => {
                            self.bin_arith("add", ltmp.clone(), rv_str, None, rv_c, |a, b| {
                                a.wrapping_add(b)
                            })
                        }
                        BinaryOp::Minus => {
                            self.bin_arith("sub", ltmp.clone(), rv_str, None, rv_c, |a, b| {
                                a.wrapping_sub(b)
                            })
                        }
                        BinaryOp::Mul => {
                            self.bin_arith("mul", ltmp.clone(), rv_str, None, rv_c, |a, b| {
                                a.wrapping_mul(b)
                            })
                        }
                        BinaryOp::Div => {
                            self.bin_arith("sdiv", ltmp.clone(), rv_str, None, rv_c, |a, b| {
                                if b != 0 {
                                    a.wrapping_div(b)
                                } else {
                                    0
                                }
                            })
                        }
                        BinaryOp::Mod => {
                            self.bin_arith("srem", ltmp.clone(), rv_str, None, rv_c, |a, b| {
                                if b != 0 {
                                    a.wrapping_rem(b)
                                } else {
                                    0
                                }
                            })
                        }
                        BinaryOp::Shl => {
                            self.bin_arith("shl", ltmp.clone(), rv_str, None, rv_c, |a, b| {
                                a.wrapping_shl((b as u32) & 31)
                            })
                        }
                        BinaryOp::Shr => {
                            self.bin_arith("ashr", ltmp.clone(), rv_str, None, rv_c, |a, b| {
                                (a >> ((b as u32) & 31))
                            })
                        }
                        BinaryOp::BitAnd => {
                            self.bin_arith("and", ltmp.clone(), rv_str, None, rv_c, |a, b| a & b)
                        }
                        BinaryOp::BitOr => {
                            self.bin_arith("or", ltmp.clone(), rv_str, None, rv_c, |a, b| a | b)
                        }
                        BinaryOp::BitXor => {
                            self.bin_arith("xor", ltmp.clone(), rv_str, None, rv_c, |a, b| a ^ b)
                        }
                        _ => (ltmp.clone(), None),
                    };
                    let _ = writeln!(self.buf, "  store i32 {}, ptr {}", res_str, pstr);
                    self.consts.clear();
                    (res_str, None)
                }
                _ => self.emit_expr(rhs),
            },
            // Sized queries
            Expr::SizeofType(ty) => {
                let sz = self.sizeof_t(ty);
                (format!("{}", sz), Some(sz))
            }
            Expr::SizeofExpr(expr) => {
                let sz = match &**expr {
                    // sizeof on an identifier should use its declared type without array-to-pointer decay
                    Expr::Ident(name) => match self.locals_ty.get(name) {
                        Some(ty) => self.sizeof_t(ty),
                        None => 4,
                    },
                    // sizeof string literal = length including NUL terminator
                    Expr::StringLiteral(repr) => decode_c_string(repr).len() as i32,
                    // sizeof(&expr) => pointer size
                    Expr::Unary {
                        op: UnaryOp::AddrOf,
                        ..
                    } => 8,
                    // sizeof(*expr) => sizeof(int) for our supported pointee
                    Expr::Unary {
                        op: UnaryOp::Deref, ..
                    } => 4,
                    // sizeof on a cast expression uses the target type
                    Expr::Cast { ty, .. } => self.sizeof_t(ty),
                    // sizeof on an indexing expression yields element size (int)
                    Expr::Index { .. } => 4,
                    // Fallback: use pointer heuristic vs int
                    _ => {
                        if self.expr_is_pointer(&**expr) {
                            8
                        } else {
                            4
                        }
                    }
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
                // Determine declared type of the LHS identifier (local preferred)
                let lhs_ty = self
                    .locals_ty
                    .get(name)
                    .cloned()
                    .or_else(|| self.global_types.get(name).cloned())
                    .unwrap_or(Type::Int);

                // If assigning to a struct/union object, emit memcpy instead of scalar store
                let memcpy_struct_union = matches!(lhs_ty, Type::Struct(_) | Type::Union(_));
                if memcpy_struct_union {
                    // Compute destination pointer for the LHS identifier
                    let dst_ptr = if let Some(p) = self.locals.get(name).cloned() {
                        p
                    } else {
                        // Fallback: create storage for an undeclared local (should not normally happen)
                        let alloca_name = format!("%{}.addr", name);
                        let sz = match &lhs_ty {
                            Type::Struct(tag) => self
                                .struct_layouts
                                .get(tag)
                                .map(|l| l.size)
                                .unwrap_or(0),
                            Type::Union(tag) => self
                                .union_layouts
                                .get(tag)
                                .map(|l| l.size)
                                .unwrap_or(0),
                            _ => 0,
                        };
                        let _ = writeln!(
                            self.buf,
                            "  {} = alloca i8, i64 {}",
                            alloca_name, sz
                        );
                        self.locals.insert(name.clone(), alloca_name.clone());
                        self.locals_ty.insert(name.clone(), lhs_ty.clone());
                        alloca_name
                    };

                    // Compute source pointer for RHS lvalue of the same type
                    let src_ptr_opt: Option<String> = match &**value {
                        Expr::Ident(n2) => {
                            if let Some(p) = self.locals.get(n2).cloned() {
                                Some(p)
                            } else if self.global_types.contains_key(n2) {
                                Some(format!("@{}", n2))
                            } else {
                                None
                            }
                        }
                        Expr::Unary { op: UnaryOp::Deref, expr } => {
                            let (pstr, _pc) = self.emit_expr(expr);
                            Some(pstr)
                        }
                        Expr::Index { base, index } => {
                            let (ptr, _ety) = self.emit_index_ptr(base, index);
                            Some(ptr)
                        }
                        Expr::Member { base, field, arrow } => {
                            let (ptr, _fty) = self.emit_member_ptr(base, field, *arrow);
                            Some(ptr)
                        }
                        _ => None,
                    };

                    if let Some(src_ptr) = src_ptr_opt {
                        // Determine size from type
                        let sz = match &lhs_ty {
                            Type::Struct(tag) => self
                                .struct_layouts
                                .get(tag)
                                .map(|l| l.size)
                                .unwrap_or(0),
                            Type::Union(tag) => self
                                .union_layouts
                                .get(tag)
                                .map(|l| l.size)
                                .unwrap_or(0),
                            _ => 0,
                        } as i64;
                        // Declare memcpy once and emit call
                        self.add_decl("declare void @llvm.memcpy.p0.p0.i64(ptr nocapture writeonly, ptr nocapture readonly, i64, i1 immarg)");
                        let _ = writeln!(
                            self.buf,
                            "  call void @llvm.memcpy.p0.p0.i64(ptr {}, ptr {}, i64 {}, i1 false)",
                            dst_ptr, src_ptr, sz
                        );
                        self.consts.remove(name);
                        return ("0".to_string(), Some(0));
                    } else {
                        // Fallback: evaluate RHS (no-op store), return 0
                        let (_vstr, _vc) = self.emit_expr(value);
                        self.consts.remove(name);
                        return ("0".to_string(), Some(0));
                    }
                }

                // Scalar or pointer path (previous behavior)
                let (vstr, vc) = self.emit_expr(value);
                let ptr = if let Some(p) = self.locals.get(name) {
                    p.clone()
                } else {
                    let p = format!("%{}.addr", name);
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
                        if let Some(c) = vc {
                            self.consts.insert(name.clone(), c);
                        } else {
                            self.consts.remove(name);
                        }
                    }
                }
                (vstr, vc)
            }
            // Store assignment through pointer; support struct/union copies via memcpy
            Expr::AssignDeref { ptr: pexpr, value } => {
                // Determine the pointee type of *pexpr
                let dst_val_ty = self
                    .type_of_expr(&Expr::Unary { op: UnaryOp::Deref, expr: pexpr.clone() })
                    .unwrap_or(Type::Int);

                if matches!(dst_val_ty, Type::Struct(_) | Type::Union(_)) {
                    // Destination pointer (already a ptr value)
                    let (dst_ptr, _pc) = self.emit_expr(pexpr);
                    // Source pointer from RHS lvalue
                    let src_ptr_opt: Option<String> = match &**value {
                        Expr::Ident(n2) => {
                            if let Some(p) = self.locals.get(n2).cloned() {
                                Some(p)
                            } else if self.global_types.contains_key(n2) {
                                Some(format!("@{}", n2))
                            } else {
                                None
                            }
                        }
                        Expr::Unary { op: UnaryOp::Deref, expr } => {
                            let (pstr, _pc) = self.emit_expr(expr);
                            Some(pstr)
                        }
                        Expr::Index { base, index } => {
                            let (ptr, _ety) = self.emit_index_ptr(base, index);
                            Some(ptr)
                        }
                        Expr::Member { base, field, arrow } => {
                            let (ptr, _fty) = self.emit_member_ptr(base, field, *arrow);
                            Some(ptr)
                        }
                        _ => None,
                    };
                    if let Some(src_ptr) = src_ptr_opt {
                        let sz = match &dst_val_ty {
                            Type::Struct(tag) => self
                                .struct_layouts
                                .get(tag)
                                .map(|l| l.size)
                                .unwrap_or(0),
                            Type::Union(tag) => self
                                .union_layouts
                                .get(tag)
                                .map(|l| l.size)
                                .unwrap_or(0),
                            _ => 0,
                        } as i64;
                        self.add_decl("declare void @llvm.memcpy.p0.p0.i64(ptr nocapture writeonly, ptr nocapture readonly, i64, i1 immarg)");
                        let _ = writeln!(
                            self.buf,
                            "  call void @llvm.memcpy.p0.p0.i64(ptr {}, ptr {}, i64 {}, i1 false)",
                            dst_ptr, src_ptr, sz
                        );
                        self.consts.clear();
                        return ("0".to_string(), Some(0));
                    } else {
                        let (_vstr, _vc) = self.emit_expr(value);
                        self.consts.clear();
                        return ("0".to_string(), Some(0));
                    }
                }

                // Fallback scalar store behavior
                let (pstr, _pc) = self.emit_expr(pexpr);
                let (vstr, _vc) = self.emit_expr(value);
                let _ = writeln!(self.buf, "  store i32 {}, ptr {}", vstr, pstr);
                self.consts.clear();
                (vstr, None)
            },
            // Initializer lists are not evaluatable as rvalues here; treat as zero
            Expr::InitList(_items) => ("0".to_string(), Some(0)),
        }
    }
    fn bin_arith<F: Fn(i32, i32) -> i32>(
        &mut self,
        op: &str,
        l: String,
        r: String,
        _lc: Option<i32>,
        _rc: Option<i32>,
        _f: F,
    ) -> (String, Option<i32>) {
        // Do not constant-fold here; tests rely on presence of specific ops (ashr/sdiv/srem)
        let tmp = self.new_tmp();
        let _ = writeln!(self.buf, "  {} = {} i32 {}, {}", tmp, op, l, r);
        (tmp, None)
    }
    fn emit_stmt(&mut self, s: &Stmt, ret_ty: &Type) {
        // If the current basic block already has a terminator, only a label
        // can legally start a new block; other statements must be ignored.
        if self.terminated {
            if !matches!(s, Stmt::Label(_)) {
                return;
            }
        }
        match s {
            Stmt::Block(stmts) => {
                if self.terminated {
                    return;
                }
                for st in stmts {
                    self.emit_stmt(st, ret_ty);
                    if self.terminated {
                        break;
                    }
                }
            }
            Stmt::If {
                cond,
                then_branch,
                else_branch,
            } => {
                if self.terminated {
                    return;
                }
                let (cv_str, cv_c) = self.emit_expr(cond);
                let (c_i1, _c_b) = self.to_bool(cv_str, cv_c);
                let then_lbl = self.new_label();
                let cont_lbl = self.new_label();
                let else_lbl = if else_branch.is_some() {
                    Some(self.new_label())
                } else {
                    None
                };
                if let Some(el) = &else_lbl {
                    self.br_cond(&c_i1, &then_lbl, el);
                } else {
                    self.br_cond(&c_i1, &then_lbl, &cont_lbl);
                }
                // then
                self.start_block(&then_lbl);
                for st in then_branch {
                    self.emit_stmt(st, ret_ty);
                    if self.terminated {
                        break;
                    }
                }
                if !self.terminated {
                    self.br_uncond(&cont_lbl);
                }
                // else
                if let Some(el) = else_lbl {
                    self.start_block(&el);
                    if let Some(eb) = else_branch {
                        for st in eb {
                            self.emit_stmt(st, ret_ty);
                            if self.terminated {
                                break;
                            }
                        }
                    }
                    if !self.terminated {
                        self.br_uncond(&cont_lbl);
                    }
                }
                // cont
                self.start_block(&cont_lbl);
            }
            Stmt::While { cond, body } => {
                if self.terminated {
                    return;
                }
                let cond_lbl = self.new_label();
                let body_lbl = self.new_label();
                let end_lbl = self.new_label();
                self.loop_stack.push((end_lbl.clone(), cond_lbl.clone()));
                self.in_loop += 1;
                self.br_uncond(&cond_lbl);
                self.start_block(&cond_lbl);
                let (cv_str, cv_c) = self.emit_expr(cond);
                let (c_i1, _c_b) = self.to_bool(cv_str, cv_c);
                self.br_cond(&c_i1, &body_lbl, &end_lbl);
                self.start_block(&body_lbl);
                for st in body {
                    self.emit_stmt(st, ret_ty);
                    if self.terminated {
                        break;
                    }
                }
                if !self.terminated {
                    self.br_uncond(&cond_lbl);
                }
                self.in_loop -= 1;
                let _ = self.loop_stack.pop();
                self.start_block(&end_lbl);
            }
            Stmt::DoWhile { body, cond } => {
                if self.terminated {
                    return;
                }
                let body_lbl = self.new_label();
                let cond_lbl = self.new_label();
                let end_lbl = self.new_label();
                self.loop_stack.push((end_lbl.clone(), cond_lbl.clone()));
                self.in_loop += 1;
                self.br_uncond(&body_lbl);
                self.start_block(&body_lbl);
                for st in body {
                    self.emit_stmt(st, ret_ty);
                    if self.terminated {
                        break;
                    }
                }
                if !self.terminated {
                    self.br_uncond(&cond_lbl);
                }
                self.start_block(&cond_lbl);
                let (cv_str, cv_c) = self.emit_expr(cond);
                let (c_i1, _c_b) = self.to_bool(cv_str, cv_c);
                self.br_cond(&c_i1, &body_lbl, &end_lbl);
                self.in_loop -= 1;
                let _ = self.loop_stack.pop();
                self.start_block(&end_lbl);
            }
            Stmt::For {
                init,
                cond,
                post,
                body,
            } => {
                if self.terminated {
                    return;
                }
                if let Some(e) = init {
                    let _ = self.emit_expr(e);
                }
                let cond_lbl = self.new_label();
                let body_lbl = self.new_label();
                let post_lbl = self.new_label();
                let end_lbl = self.new_label();
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
                for st in body {
                    self.emit_stmt(st, ret_ty);
                    if self.terminated {
                        break;
                    }
                }
                if !self.terminated {
                    self.br_uncond(&post_lbl);
                }
                self.start_block(&post_lbl);
                if let Some(p) = post {
                    let _ = self.emit_expr(p);
                }
                self.br_uncond(&cond_lbl);
                self.start_block(&end_lbl);
            }
            Stmt::Switch { cond, body } => {
                if self.terminated {
                    return;
                }
                let (cstr, _cc) = self.emit_expr(cond);
                let end_lbl = self.new_label();
                let dispatch_lbl = self.new_label();
                // discover labels
                let mut labels: Vec<(String, Option<&Expr>)> = Vec::new();
                let mut label_indices: Vec<usize> = Vec::new();
                for (i, s2) in body.iter().enumerate() {
                    match s2 {
                        Stmt::Case { value } => {
                            let l = self.new_label();
                            labels.push((l, Some(value)));
                            label_indices.push(i);
                        }
                        Stmt::Default => {
                            let l = self.new_label();
                            labels.push((l, None));
                            label_indices.push(i);
                        }
                        _ => {}
                    }
                }
                self.br_uncond(&dispatch_lbl);
                let mut block_starts: HashMap<usize, String> = HashMap::new();
                for (i, idx) in label_indices.iter().enumerate() {
                    let lbl = labels[i].0.clone();
                    block_starts.insert(*idx, lbl);
                }
                let mut i = 0;
                while i < body.len() {
                    if let Some(lbl) = block_starts.get(&i).cloned() {
                        self.start_block(&lbl);
                        i += 1;
                        while i < body.len() {
                            if block_starts.contains_key(&i) {
                                break;
                            }
                            if let Stmt::Break = body[i] {
                                self.br_uncond(&end_lbl);
                                i += 1;
                                break;
                            }
                            self.emit_stmt(&body[i], ret_ty);
                            i += 1;
                        }
                        if !self.terminated {
                            self.br_uncond(&end_lbl);
                        }
                        continue;
                    }
                    i += 1;
                }
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
                            let _ =
                                writeln!(self.buf, "  {} = icmp eq i32 {}, {}", cmp, cstr, val_str);
                            let next_lbl = self.new_label();
                            self.br_cond(&cmp, lbl, &next_lbl);
                            self.start_block(&next_lbl);
                        }
                        jumped = true;
                    } else {
                        if !jumped {
                            self.br_uncond(lbl);
                            jumped = true;
                        }
                    }
                }
                if !jumped {
                    self.br_uncond(&end_lbl);
                }
                self.start_block(&end_lbl);
            }
            Stmt::Break => {
                if let Some((break_lbl, _cont_lbl)) = self
                    .loop_stack
                    .last()
                    .cloned()
                    .or_else(|| self.switch_stack.last().map(|l| (l.clone(), String::new())))
                {
                    self.br_uncond(&break_lbl);
                }
            }
            Stmt::Continue => {
                if let Some((_break_lbl, cont_lbl)) = self.loop_stack.last().cloned() {
                    self.br_uncond(&cont_lbl);
                }
            }
            Stmt::Return(e) => {
                if self.terminated {
                    return;
                }
                let (val_str, _cval) = self.emit_expr(e);
                match ret_ty {
                    Type::Void => {
                        let _ = writeln!(self.buf, "  ret void");
                    }
                    _ => {
                        let _ = writeln!(self.buf, "  ret i32 {}", val_str);
                    }
                }
                self.terminated = true;
            }
            Stmt::Decl {
                name,
                ty,
                init,
                storage,
                ..
            } => {
                // Function-scope static local: emit module-scope internal global and map ident to @global
                if matches!(storage, Some(parse::ast::Storage::Static)) {
                    let gname = format!("__static_{}_{}", self.current_fn, name);
                    if self.static_locals_emitted.insert(gname.clone()) {
                        match ty {
                            Type::Pointer(_) => {
                                let init_val = if let Some(e) = init {
                                    match e {
                                        Expr::StringLiteral(repr) => {
                                            let (sname, len) =
                                                self.ensure_string_global_from_repr(repr);
                                            format!(
                                                "getelementptr inbounds ([{} x i8], ptr {}, i64 0, i64 0)",
                                                len, sname
                                            )
                                        }
                                        Expr::Cast { expr, .. } => {
                                            if let Expr::StringLiteral(repr) = &**expr {
                                                let (sname, len) =
                                                    self.ensure_string_global_from_repr(repr);
                                                format!(
                                                    "getelementptr inbounds ([{} x i8], ptr {}, i64 0, i64 0)",
                                                    len, sname
                                                )
                                            } else {
                                                "null".to_string()
                                            }
                                        }
                                        Expr::IntLiteral(s) => {
                                            if parse_int_repr(s) == 0 {
                                                "null".to_string()
                                            } else {
                                                "null".to_string()
                                            }
                                        }
                                        _ => "null".to_string(),
                                    }
                                } else {
                                    "null".to_string()
                                };
                                let def = format!("@{} = internal global ptr {}", gname, init_val);
                                self.globals.push(def);
                            }
                            _ => {
                                let init_str = if let Some(Expr::IntLiteral(repr)) = init {
                                    format!("{}", parse_int_repr(repr))
                                } else {
                                    "zeroinitializer".to_string()
                                };
                                let def = format!("@{} = internal global i32 {}", gname, init_str);
                                self.globals.push(def);
                            }
                        }
                    }
                    // Map local name to the global pointer; subsequent loads/stores use @global
                    self.locals.insert(name.clone(), format!("@{}", gname));
                    self.locals_ty.insert(name.clone(), ty.clone());
                    self.consts.remove(name);
                } else {
                    match ty {
                        Type::Array(inner, n) => {
                            let alloca_name = format!("%{}", name);
                            // Track if we allocated a typed array and, for i8 arrays, its length
                            let mut used_typed_arr = false;
                            let mut typed_i8_len: Option<usize> = None;

                            // Precompute effective char array length for unsized char[] initialized from a string literal
                            if matches!(&**inner, Type::Char | Type::SChar | Type::UChar) {
                                if *n == 0 {
                                    if let Some(e) = init {
                                        match e {
                                            Expr::StringLiteral(repr) => {
                                                typed_i8_len = Some(decode_c_string(repr).len());
                                            }
                                            Expr::Cast { expr: inner_e, .. } => {
                                                if let Expr::StringLiteral(repr2) = &**inner_e {
                                                    typed_i8_len = Some(decode_c_string(repr2).len());
                                                }
                                            }
                                            _ => {}
                                        }
                                    }
                                }
                            }

                            // Decide alloca type
                            if let Some(arr_str) = self.llvm_int_array_type_str(ty) {
                                // Typed nested int arrays
                                let _ = writeln!(self.buf, "  {} = alloca {}", alloca_name, arr_str);
                                used_typed_arr = true;
                            } else if matches!(&**inner, Type::Char | Type::SChar | Type::UChar) {
                                // typed [len x i8] for char arrays; for unsized + string init, infer len from literal
                                let alloc_len: usize = if *n == 0 {
                                    typed_i8_len.unwrap_or(0)
                                } else {
                                    *n
                                };
                                if alloc_len > 0 {
                                    let ty_str = format!("[{} x i8]", alloc_len);
                                    let _ = writeln!(self.buf, "  {} = alloca {}", alloca_name, ty_str);
                                    used_typed_arr = true;
                                    typed_i8_len = Some(alloc_len);
                                } else {
                                    let total_sz = self.sizeof_t_usize(ty);
                                    let _ = writeln!(self.buf, "  {} = alloca i8, i64 {}", alloca_name, total_sz);
                                }
                            } else {
                                let total_sz = self.sizeof_t_usize(ty);
                                let _ = writeln!(
                                    self.buf,
                                    "  {} = alloca i8, i64 {}",
                                    alloca_name, total_sz
                                );
                            }
                            self.locals.insert(name.clone(), alloca_name.clone());
                            self.locals_ty.insert(name.clone(), ty.clone());

                            // Initialization for local arrays
                            if let Some(e) = init {
                                // Zero-fill entire aggregate first (best-effort if size is known from declared type)
                                let total_sz = self.sizeof_t_usize(ty) as i64;
                                self.add_decl("declare void @llvm.memset.p0.i64(ptr nocapture writeonly, i8, i64, i1 immarg)");
                                let _ = writeln!(
                                    self.buf,
                                    "  call void @llvm.memset.p0.i64(ptr {}, i8 0, i64 {}, i1 false)",
                                    alloca_name, total_sz
                                );

                                match (&**inner, e) {
                                    // char array from string literal -> memcpy of literal bytes (incl NUL)
                                    (Type::Char | Type::SChar | Type::UChar, Expr::StringLiteral(repr)) => {
                                        let (gname, len) = self.ensure_string_global_from_repr(repr);
                                        let dst = if used_typed_arr {
                                            let p = self.new_tmp();
                                            // Use the actual typed length if we inferred it for unsized arrays, else declared n
                                            let ty_len = typed_i8_len.unwrap_or(*n);
                                            let _ = writeln!(
                                                self.buf,
                                                "  {} = getelementptr inbounds [{} x i8], ptr {}, i64 0, i64 0",
                                                p, ty_len, alloca_name
                                            );
                                            p
                                        } else {
                                            alloca_name.clone()
                                        };
                                        let src = self.new_tmp();
                                        let _ = writeln!(
                                            self.buf,
                                            "  {} = getelementptr inbounds [{} x i8], ptr {}, i64 0, i64 0",
                                            src, len, gname
                                        );
                                        self.add_decl("declare void @llvm.memcpy.p0.p0.i64(ptr nocapture writeonly, ptr nocapture readonly, i64, i1 immarg)");
                                        let _ = writeln!(
                                            self.buf,
                                            "  call void @llvm.memcpy.p0.p0.i64(ptr {}, ptr {}, i64 {}, i1 false)",
                                            dst, src, len
                                        );
                                    }
                                    (Type::Char | Type::SChar | Type::UChar, Expr::Cast { expr: inner_e, .. }) => {
                                        if let Expr::StringLiteral(repr) = &**inner_e {
                                            let (gname, len) = self.ensure_string_global_from_repr(repr);
                                            let dst = if used_typed_arr {
                                                let p = self.new_tmp();
                                                let ty_len = typed_i8_len.unwrap_or(*n);
                                                let _ = writeln!(
                                                    self.buf,
                                                    "  {} = getelementptr inbounds [{} x i8], ptr {}, i64 0, i64 0",
                                                    p, ty_len, alloca_name
                                                );
                                                p
                                            } else {
                                                alloca_name.clone()
                                            };
                                            let src = self.new_tmp();
                                            let _ = writeln!(
                                                self.buf,
                                                "  {} = getelementptr inbounds [{} x i8], ptr {}, i64 0, i64 0",
                                                src, len, gname
                                            );
                                            self.add_decl("declare void @llvm.memcpy.p0.p0.i64(ptr nocapture writeonly, ptr nocapture readonly, i64, i1 immarg)");
                                            let _ = writeln!(
                                                self.buf,
                                                "  call void @llvm.memcpy.p0.p0.i64(ptr {}, ptr {}, i64 {}, i1 false)",
                                                dst, src, len
                                            );
                                        }
                                    }
                                    // int arrays with initializer list -> element stores
                                    (_, Expr::InitList(items)) => {
                                        if matches!(&**inner, Type::Int | Type::UInt | Type::Long | Type::ULong | Type::Short | Type::UShort | Type::Enum(_) | Type::Named(_)) {
                                            for (i, it) in items.iter().enumerate() {
                                                if i >= *n { break; }
                                                // element pointer
                                                let eptr = if used_typed_arr {
                                                    let p = self.new_tmp();
                                                    let _ = writeln!(
                                                        self.buf,
                                                        "  {} = getelementptr inbounds [{} x i32], ptr {}, i64 0, i64 {}",
                                                        p, n, alloca_name, i
                                                    );
                                                    p
                                                } else {
                                                    let off = (i as i64) * 4;
                                                    let p = self.new_tmp();
                                                    let _ = writeln!(
                                                        self.buf,
                                                        "  {} = getelementptr inbounds i8, ptr {}, i64 {}",
                                                        p, alloca_name, off
                                                    );
                                                    p
                                                };
                                                // value
                                                let vstr = if let Expr::IntLiteral(repr) = it {
                                                    format!("{}", parse_int_repr(repr))
                                                } else {
                                                    let (vs, _vc) = self.emit_expr(it);
                                                    vs
                                                };
                                                let _ = writeln!(self.buf, "  store i32 {}, ptr {}", vstr, eptr);
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                            }
                            self.consts.remove(name);
                        }
                        Type::Pointer(inner) => {
                            let alloca_name = format!("%{}", name);
                            let _ = writeln!(self.buf, "  {} = alloca ptr", alloca_name);
                            self.locals.insert(name.clone(), alloca_name.clone());
                            self.locals_ty
                                .insert(name.clone(), Type::Pointer(inner.clone()));
                            if let Some(e) = init {
                                let (val_str, _cval) = self.emit_expr(e);
                                let _ = writeln!(
                                    self.buf,
                                    "  store ptr {}, ptr {}",
                                    val_str, alloca_name
                                );
                            }
                            self.consts.remove(name);
                        }
                        Type::Struct(tag) => {
                            let alloca_name = format!("%{}", name);
                            let sz = self.struct_layouts.get(tag).map(|l| l.size).unwrap_or(8);
                            let _ = writeln!(self.buf, "  {} = alloca i8, i64 {}", alloca_name, sz);
                            self.locals.insert(name.clone(), alloca_name.clone());
                            self.locals_ty
                                .insert(name.clone(), Type::Struct(tag.clone()));

                            if let Some(e) = init {
                                // Zero-fill struct
                                self.add_decl("declare void @llvm.memset.p0.i64(ptr nocapture writeonly, i8, i64, i1 immarg)");
                                let _ = writeln!(
                                    self.buf,
                                    "  call void @llvm.memset.p0.i64(ptr {}, i8 0, i64 {}, i1 false)",
                                    alloca_name,
                                    sz as i64
                                );
                                // Field stores for simple int and array-of-int fields from list
                                if let Expr::InitList(items) = e {
                                    if let Some(sl) = self.struct_layouts.get(tag) {
                                        // order members by offset
                                        let mut ordered: Vec<(usize, Type)> = sl
                                            .members
                                            .iter()
                                            .map(|(_n, (off, ty))| (*off, ty.clone()))
                                            .collect();
                                        ordered.sort_by_key(|(o, _)| *o);
                                        for (i, (off, fty)) in ordered.iter().enumerate() {
                                            if i >= items.len() { break; }
                                            let it = &items[i];
                                            match fty {
                                                // scalar int-like field
                                                Type::Int | Type::UInt | Type::Long | Type::ULong | Type::Short | Type::UShort | Type::Enum(_) | Type::Named(_) | Type::Char | Type::SChar | Type::UChar => {
                                                    let fptr = self.new_tmp();
                                                    let _ = writeln!(
                                                        self.buf,
                                                        "  {} = getelementptr inbounds i8, ptr {}, i64 {}",
                                                        fptr, alloca_name, *off as i64
                                                    );
                                                    let vstr = if let Expr::IntLiteral(repr) = it {
                                                        format!("{}", parse_int_repr(repr))
                                                    } else {
                                                        let (vs, _vc) = self.emit_expr(it);
                                                        vs
                                                    };
                                                    let _ = writeln!(self.buf, "  store i32 {}, ptr {}", vstr, fptr);
                                                }
                                                // array-of-int field with nested initializer list
                                                Type::Array(inner2, n2) if matches!(&**inner2, Type::Int | Type::UInt | Type::Long | Type::ULong | Type::Short | Type::UShort | Type::Enum(_) | Type::Named(_)) => {
                                                    if let Expr::InitList(vs) = it {
                                                        let esz = self.sizeof_t_usize(&inner2) as i64; // 4 for int
                                                        for (j, v) in vs.iter().enumerate() {
                                                            if j >= *n2 { break; }
                                                            let elem_off = (*off as i64) + (j as i64) * esz;
                                                            let eptr = self.new_tmp();
                                                            let _ = writeln!(
                                                                self.buf,
                                                                "  {} = getelementptr inbounds i8, ptr {}, i64 {}",
                                                                eptr, alloca_name, elem_off
                                                            );
                                                            let vstr = if let Expr::IntLiteral(repr) = v {
                                                                format!("{}", parse_int_repr(repr))
                                                            } else {
                                                                let (vs, _vc) = self.emit_expr(v);
                                                                vs
                                                            };
                                                            let _ = writeln!(self.buf, "  store i32 {}, ptr {}", vstr, eptr);
                                                        }
                                                    }
                                                }
                                                _ => { /* unsupported nested type for v1 */ }
                                            }
                                        }
                                    }
                                }
                            }
                            self.consts.remove(name);
                        }
                        Type::Union(tag) => {
                            let alloca_name = format!("%{}", name);
                            let sz = self.union_layouts.get(tag).map(|l| l.size).unwrap_or(8);
                            let _ = writeln!(self.buf, "  {} = alloca i8, i64 {}", alloca_name, sz);
                            self.locals.insert(name.clone(), alloca_name.clone());
                            self.locals_ty
                                .insert(name.clone(), Type::Union(tag.clone()));
                            if let Some(_e) = init { /* aggregate init limited in v1 */ }
                            self.consts.remove(name);
                        }
                        _ => {
                            let alloca_name = format!("%{}", name);
                            let _ = writeln!(self.buf, "  {} = alloca i32", alloca_name);
                            self.locals.insert(name.clone(), alloca_name.clone());
                            self.locals_ty.insert(name.clone(), ty.clone());
                            if let Some(e) = init {
                                let (val_str, cval) = self.emit_expr(e);
                                let _ = writeln!(
                                    self.buf,
                                    "  store i32 {}, ptr {}",
                                    val_str, alloca_name
                                );
                                if let Some(c) = cval {
                                    self.consts.insert(name.clone(), c);
                                } else {
                                    self.consts.remove(name);
                                }
                            }
                        }
                    }
                }
            }
            Stmt::Case { .. } => { /* handled within Switch lowering */ }
            Stmt::Default => { /* handled within Switch lowering */ }
            Stmt::Typedef { .. } => { /* no runtime effect */ }
            Stmt::Label(name) => {
                let lbl = self.ensure_user_label(name);
                if self.in_block && !self.terminated {
                    self.br_uncond(&lbl);
                }
                self.start_block(&lbl);
            }
            Stmt::Goto(name) => {
                let lbl = self.ensure_user_label(name);
                self.br_uncond(&lbl);
            }
            Stmt::ExprStmt(e) => {
                let _ = self.emit_expr(e);
            }
        }
    }
}

fn round_up(x: usize, align: usize) -> usize {
    if align == 0 {
        return x;
    }
    let rem = x % align;
    if rem == 0 {
        x
    } else {
        x + (align - rem)
    }
}

fn parse_int_repr(repr: &str) -> i32 {
    let mut s = repr.trim();
    // strip simple integer suffixes (u/U/l/L)
    loop {
        if let Some(ch) = s.chars().last() {
            if matches!(ch, 'u' | 'U' | 'l' | 'L') {
                s = &s[..s.len() - 1];
                continue;
            }
        }
        break;
    }
    let neg = s.starts_with('-');
    let body = if neg { &s[1..] } else { s };
    let v64: i64 = if body.starts_with("0x") || body.starts_with("0X") {
        i64::from_str_radix(&body[2..], 16).unwrap_or(0)
    } else if body.starts_with('0') && body.len() > 1 {
        i64::from_str_radix(&body[1..], 8).unwrap_or(0)
    } else {
        body.parse::<i64>().unwrap_or(0)
    };
    let v = if neg { -v64 } else { v64 };
    v as i32
}

fn decode_c_string(repr: &str) -> Vec<u8> {
    let mut bytes: Vec<u8> = Vec::new();
    let mut esc = false;
    let cs: Vec<char> = repr.chars().collect();
    let mut i = 0usize;
    // Skip leading quote if present
    if !cs.is_empty() && cs[0] == '"' {
        i = 1;
    }
    while i < cs.len() {
        let ch = cs[i];
        if !esc {
            if ch == '"' {
                break;
            }
            if ch == '\\' {
                esc = true;
                i += 1;
                continue;
            }
            bytes.push(ch as u8);
            i += 1;
            continue;
        }
        // escape mode
        esc = false;
        match ch {
            'n' => bytes.push(b'\n'),
            'r' => bytes.push(b'\r'),
            't' => bytes.push(b'\t'),
            '\\' => bytes.push(b'\\'),
            '"' => bytes.push(b'"'),
            'x' | 'X' => {
                // up to two hex digits
                let mut val: u8 = 0;
                let mut cnt = 0;
                while i + 1 < cs.len() && cnt < 2 {
                    let c = cs[i + 1];
                    if let Some(dv) = c.to_digit(16) {
                        val = (val << 4) | (dv as u8);
                        cnt += 1;
                        i += 1;
                    } else {
                        break;
                    }
                }
                bytes.push(val);
            }
            '0'..='7' => {
                // up to three octal digits (first already in ch)
                let mut val: u16 = (ch as u16) - ('0' as u16);
                let mut cnt = 1;
                while i + 1 < cs.len() && cnt < 3 {
                    let c = cs[i + 1];
                    if let '0'..='7' = c {
                        val = (val << 3) | ((c as u16) - ('0' as u16));
                        cnt += 1;
                        i += 1;
                    } else {
                        break;
                    }
                }
                bytes.push((val & 0xFF) as u8);
            }
            _ => {
                bytes.push(ch as u8);
            }
        }
        i += 1;
    }
    // NUL-terminate C string
    bytes.push(0);
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
        if line.is_empty() {
            continue;
        }
        if line.starts_with(';') {
            continue;
        }

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
            if saw_term {
                return Err(anyhow!("multiple terminators in block"));
            }
            saw_term = true;
            continue;
        }
        if line.starts_with("br ") {
            if saw_term {
                return Err(anyhow!("multiple terminators in block"));
            }
            // collect targets
            // br label %X
            if let Some(idx) = line.find("label %") {
                let rest = &line[idx + "label %".len()..];
                let mut parts = rest.split(|c| c == ',' || c == ' ');
                if let Some(t) = parts.next() {
                    let t = t.trim();
                    if !t.is_empty() {
                        branch_targets.push(t.to_string());
                    }
                }
                // br i1 ..., label %T, label %E
                if let Some(idx2) = line.rfind("label %") {
                    if idx2 != idx {
                        let rest2 = &line[idx2 + "label %".len()..];
                        let t2 = rest2
                            .split(|c| c == ',' || c == ' ')
                            .next()
                            .unwrap_or("")
                            .trim();
                        if !t2.is_empty() {
                            branch_targets.push(t2.to_string());
                        }
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