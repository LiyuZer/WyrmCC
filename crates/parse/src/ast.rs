#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    Void,
    Pointer(Box<Type>),
    Array(Box<Type>, usize),
    // C89 aggregate and named types (tags and typedef-names)
    Struct(String),
    Union(String),
    Enum(String),
    Named(String), // typedef-name to be resolved in sema
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub name: String,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnaryOp {
    Plus,
    Minus,
    BitNot,
    LogicalNot,
    AddrOf,
    Deref,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinaryOp {
    // Arithmetic
    Plus,
    Minus,
    Mul,
    Div,
    Mod,
    // Shifts
    Shl,
    Shr,
    // Bitwise
    BitAnd,
    BitOr,
    BitXor,
    // Logical
    LAnd,
    LOr,
    // Comparisons (result is int 0/1)
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Ident(String),
    IntLiteral(String),
    StringLiteral(String),

    // Existing unary/binary and assignments
    Unary { op: UnaryOp, expr: Box<Expr> },
    Binary { op: BinaryOp, lhs: Box<Expr>, rhs: Box<Expr> },
    Assign { name: String, value: Box<Expr> },
    AssignDeref { ptr: Box<Expr>, value: Box<Expr> },
    Call { callee: String, args: Vec<Expr> },

    // Array indexing a[i]
    Index { base: Box<Expr>, index: Box<Expr> },

    // Member access s.a or p->a
    Member { base: Box<Expr>, field: String, arrow: bool },

    // Operators and forms
    // (type) expr
    Cast { ty: Type, expr: Box<Expr> },
    // sizeof(type)
    SizeofType(Type),
    // sizeof expr
    SizeofExpr(Box<Expr>),
    // ++/-- (pre/post); inc=true for ++, false for --; pre=true for prefix, false for postfix
    IncDec { pre: bool, inc: bool, target: Box<Expr> },
    // Compound assignment: lhs op= rhs (e.g., +=, -=, etc.)
    AssignOp { op: BinaryOp, lhs: Box<Expr>, rhs: Box<Expr> },
    // Conditional operator: cond ? then_e : else_e
    Cond { cond: Box<Expr>, then_e: Box<Expr>, else_e: Box<Expr> },
    // Comma operator: evaluate lhs then rhs; value is rhs
    Comma { lhs: Box<Expr>, rhs: Box<Expr> },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    // Control-flow and block forms
    Block(Vec<Stmt>),
    If { cond: Expr, then_branch: Vec<Stmt>, else_branch: Option<Vec<Stmt>> },
    While { cond: Expr, body: Vec<Stmt> },
    DoWhile { body: Vec<Stmt>, cond: Expr },
    For { init: Option<Expr>, cond: Option<Expr>, post: Option<Expr>, body: Vec<Stmt> },
    Break,
    Continue,

    // Switch statement and labels
    Switch { cond: Expr, body: Vec<Stmt> },
    Case { value: Expr },
    Default,

    // Existing forms
    Return(Expr),
    // typedef declaration (no runtime effect)
    Typedef { name: String, ty: Type },
    Decl { name: String, ty: Type, init: Option<Expr> },
    ExprStmt(Expr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    pub name: String,
    pub ret_type: Type,
    pub params: Vec<Param>,
    pub body: Vec<Stmt>,
}

// New: Top-level definitions captured from inline or tagged definitions
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordKind { Struct, Union }

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordDef {
    pub kind: RecordKind,
    pub tag: String,
    pub members: Vec<(String, Type)>, // (name, type)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumDef {
    pub tag: String,
    pub enumerators: Vec<(String, Option<Expr>)>, // (name, optional value expr)
}

// New: Storage class for globals (minimal)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Storage { Static, Extern }

// New: Global declaration/definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Global {
    pub name: String,
    pub ty: Type,
    pub init: Option<Expr>,
    pub storage: Option<Storage>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TranslationUnit {
    pub functions: Vec<Function>,
    pub records: Vec<RecordDef>,
    pub enums: Vec<EnumDef>,
    pub globals: Vec<Global>,
}