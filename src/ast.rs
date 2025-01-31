#[derive(Debug, Clone)]
pub enum CType {
    Void,
    Bool,
    Char,
    Int,
    Float,
    Double,
    Pointer(Box<CType>),
    Struct(String),
    Union(String),
    Enum(String),
    Array(Box<CType>, Option<usize>),
}

#[derive(Debug, Clone)]
pub struct CParam {
    pub name: String,
    pub ty: CType,
}

#[derive(Debug, Clone)]
pub enum CUnaryOp {
    Neg,
    Not,
    Tilde,
}

#[derive(Debug, Clone)]
pub enum CBinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
    And,
    Or,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

#[derive(Debug, Clone)]
pub enum CAssignOp {
    Assign,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    ModAssign,
    ShlAssign,
    ShrAssign,
    AndAssign,
    XorAssign,
    OrAssign,
}

#[derive(Debug, Clone)]
pub enum CExpr {
    LiteralInt(i64),
    LiteralFloat(f64),
    LiteralString(String),
    LiteralChar(char),
    Variable(String),
    Unary {
        op: CUnaryOp,
        expr: Box<CExpr>,
    },
    Binary {
        op: CBinaryOp,
        lhs: Box<CExpr>,
        rhs: Box<CExpr>,
    },
    Assign {
        op: CAssignOp,
        lhs: Box<CExpr>,
        rhs: Box<CExpr>,
    },
    Call {
        func: Box<CExpr>,
        args: Vec<CExpr>,
    },
    Cast {
        to: CType,
        expr: Box<CExpr>,
    },
    AddrOf(Box<CExpr>),
    Deref(Box<CExpr>),
    PostIncrement(Box<CExpr>),
    PostDecrement(Box<CExpr>),
    Ternary {
        cond: Box<CExpr>,
        then_expr: Box<CExpr>,
        else_expr: Box<CExpr>,
    },
    Member {
        base: Box<CExpr>,
        member: String,
        arrow: bool,
    },
    Subscript {
        base: Box<CExpr>,
        index: Box<CExpr>,
    },
    Comma(Vec<CExpr>),
}

#[derive(Debug, Clone)]
pub enum CStmt {
    Declaration {
        name: String,
        ty: CType,
        init: Option<CExpr>,
    },
    Expression(CExpr),
    Return(Option<CExpr>),
    If {
        cond: CExpr,
        then_branch: Box<CStmt>,
        else_branch: Option<Box<CStmt>>,
    },
    While {
        cond: CExpr,
        body: Box<CStmt>,
    },
    DoWhile {
        body: Box<CStmt>,
        cond: CExpr,
    },
    For {
        init: Option<Box<CStmt>>,
        cond: Option<CExpr>,
        increment: Option<CExpr>,
        body: Box<CStmt>,
    },
    Switch {
        expr: CExpr,
        cases: Vec<CSwitchCase>,
    },
    Break,
    Continue,
    Block(Vec<CStmt>),
}

#[derive(Debug, Clone)]
pub struct CSwitchCase {
    pub matches: Option<i64>,
    pub body: Vec<CStmt>,
}

#[derive(Debug, Clone)]
pub enum CDecl {
    Function {
        name: String,
        return_type: CType,
        params: Vec<CParam>,
        body: Vec<CStmt>,
    },
    Prototype {
        name: String,
        return_type: CType,
        params: Vec<CParam>,
    },
    GlobalVar {
        name: String,
        ty: CType,
        init: Option<CExpr>,
    },
}

#[derive(Debug, Clone)]
pub struct CFile {
    pub decls: Vec<CDecl>,
}
