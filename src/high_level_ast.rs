use crate::SourceLocation;

#[derive(Debug, Clone)]
pub enum Type {
    // Basic types
    Unit, // Similar to void but more functional
    Bool,
    Int(IntSize),     // i8, i16, i32, i64
    UInt(IntSize),    // u8, u16, u32, u64
    Float(FloatSize), // f32, f64
    String,           // String type (will be mapped to char*)

    // Complex types
    Array(Box<Type>, Option<usize>),
    Slice(Box<Type>), // Dynamic array view
    Pointer(Box<Type>),
    Reference(Box<Type>), // Safe references
    Result(Box<Type>),    // Result<T>

    // User defined types
    Struct(String),
    Enum(String),
    Distinct(String, Box<Type>), // Type with its underlying type
}

#[derive(Debug, Clone)]
pub enum IntSize {
    I8,
    I16,
    I32,
    I64,
}

#[derive(Debug, Clone)]
pub enum FloatSize {
    F32,
    F64,
}

#[derive(Debug, Clone)]
pub enum Literal {
    Int(i64),
    Float(f64),
    String(String),
    Bool(bool),
    Unit,
}

#[derive(Debug, Clone)]
pub struct Field {
    pub name: String,
    pub ty: Type,
    pub location: SourceLocation,
}

#[derive(Debug, Clone)]
pub struct StructDef {
    pub name: String,
    pub fields: Vec<Field>,
    pub location: SourceLocation,
}

#[derive(Debug, Clone)]
pub struct EnumVariant {
    pub name: String,
    pub fields: Vec<Field>,     // For variants with data
    pub value: Option<Literal>, // For explicit values like "RED"
    pub location: SourceLocation,
}

#[derive(Debug, Clone)]
pub struct EnumDef {
    pub name: String,
    pub variants: Vec<EnumVariant>,
    pub location: SourceLocation,
}

#[derive(Debug, Clone)]
pub struct DistinctDef {
    pub name: String,
    pub underlying_type: Type,
    pub location: SourceLocation,
}

#[derive(Debug, Clone)]
pub struct Parameter {
    pub name: String,
    pub ty: Type,
    pub location: SourceLocation,
}

#[derive(Debug, Clone)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    And,
    Or,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Debug, Clone)]
pub enum UnaryOp {
    Neg,
    Not,
}

#[derive(Debug, Clone)]
pub enum Pattern {
    Wildcard,         // _
    Literal(Literal), // Constants
    Variable(String), // Binding pattern
    EnumVariant {
        // Enum variant pattern
        name: String,
        fields: Vec<Pattern>,
        location: SourceLocation,
    },
    Or(Vec<Pattern>), // Multiple patterns
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Vec<Stmt>,
    pub location: SourceLocation,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Literal(Literal),
    Variable {
        name: String,
        location: SourceLocation,
    },
    Binary {
        op: BinaryOp,
        left: Box<Expr>,
        right: Box<Expr>,
        location: SourceLocation,
    },
    Unary {
        op: UnaryOp,
        expr: Box<Expr>,
        location: SourceLocation,
    },
    Call {
        func: Box<Expr>,
        args: Vec<Expr>,
        location: SourceLocation,
    },
    FieldAccess {
        expr: Box<Expr>,
        field: String,
        location: SourceLocation,
    },
    ArrayAccess {
        array: Box<Expr>,
        index: Box<Expr>,
        location: SourceLocation,
    },
    Match {
        expr: Box<Expr>,
        arms: Vec<MatchArm>,
        location: SourceLocation,
    },
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Let {
        name: String,
        ty: Option<Type>,
        value: Expr,
        location: SourceLocation,
    },
    Expr(Expr),
    Return(Option<Expr>),
    Loop {
        body: Vec<Stmt>,
        location: SourceLocation,
    },
    While {
        cond: Expr,
        body: Vec<Stmt>,
        location: SourceLocation,
    },
    Break,
    Continue,
    Block(Vec<Stmt>),
}

#[derive(Debug, Clone)]
pub enum Decl {
    Function {
        name: String,
        params: Vec<Parameter>,
        return_type: Type,
        body: Option<Vec<Stmt>>,
        location: SourceLocation,
    },
    Struct(StructDef),
    Enum(EnumDef),
    Distinct(DistinctDef),
}

#[derive(Debug, Clone)]
pub struct Module {
    pub decls: Vec<Decl>,
}

// Tests module follows...
#[cfg(test)]
mod tests {
    use super::*;
    use crate::SourceLocation;

    fn test_loc() -> SourceLocation {
        SourceLocation::new(1, 0, Some("test.c_lang".to_string()))
    }

    #[test]
    fn test_ast_locations() {
        let loc = test_loc();

        // Test function declaration with location
        let func = Decl::Function {
            name: "test".to_string(),
            params: vec![],
            return_type: Type::Int(IntSize::I32),
            body: None,
            location: loc.clone(),
        };

        match func {
            Decl::Function { location, .. } => {
                assert_eq!(location.file.as_deref().unwrap(), "test.c_lang");
                assert_eq!(location.line, 1);
            }
            _ => panic!("Expected Function declaration"),
        }
    }

    #[test]
    fn test_struct_def() {
        let struct_def = StructDef {
            name: "RGB".to_string(),
            fields: vec![
                Field {
                    name: "R".to_string(),
                    ty: Type::UInt(IntSize::I8),
                    location: test_loc(),
                },
                Field {
                    name: "G".to_string(),
                    ty: Type::UInt(IntSize::I8),
                    location: test_loc(),
                },
                Field {
                    name: "B".to_string(),
                    ty: Type::UInt(IntSize::I8),
                    location: test_loc(),
                },
            ],
            location: test_loc(),
        };

        assert_eq!(struct_def.fields.len(), 3);
    }

    #[test]
    fn test_enum_def() {
        let enum_def = EnumDef {
            name: "Color".to_string(),
            variants: vec![
                EnumVariant {
                    name: "Red".to_string(),
                    fields: vec![],
                    value: Some(Literal::String("RED".to_string())),
                    location: test_loc(),
                },
                EnumVariant {
                    name: "RGB".to_string(),
                    fields: vec![Field {
                        name: "rgb".to_string(),
                        ty: Type::Struct("RGB".to_string()),
                        location: test_loc(),
                    }],
                    value: None,
                    location: test_loc(),
                },
            ],
            location: test_loc(),
        };

        assert_eq!(enum_def.variants.len(), 2);
    }

    #[test]
    fn test_match_expr() {
        let match_expr = Expr::Match {
            expr: Box::new(Expr::Variable {
                name: "color".to_string(),
                location: test_loc(),
            }),
            arms: vec![
                MatchArm {
                    pattern: Pattern::EnumVariant {
                        name: "Red".to_string(),
                        fields: vec![],
                        location: test_loc(),
                    },
                    guard: None,
                    body: vec![],
                    location: test_loc(),
                },
                MatchArm {
                    pattern: Pattern::EnumVariant {
                        name: "RGB".to_string(),
                        fields: vec![Pattern::Variable("rgb".to_string())],
                        location: test_loc(),
                    },
                    guard: None,
                    body: vec![],
                    location: test_loc(),
                },
            ],
            location: test_loc(),
        };

        match match_expr {
            Expr::Match { arms, .. } => assert_eq!(arms.len(), 2),
            _ => panic!("Expected Match expression"),
        }
    }

    #[test]
    fn test_function_decl() {
        let func = Decl::Function {
            name: "test_func".to_string(),
            params: vec![Parameter {
                name: "a".to_string(),
                ty: Type::Int(IntSize::I32),
                location: test_loc(),
            }],
            return_type: Type::Result(Box::new(Type::Bool)),
            body: Some(vec![]),
            location: test_loc(),
        };

        match func {
            Decl::Function { params, .. } => assert_eq!(params.len(), 1),
            _ => panic!("Expected Function declaration"),
        }
    }

    #[test]
    fn test_field_access() {
        let field_access = Expr::FieldAccess {
            expr: Box::new(Expr::Variable {
                name: "MyEnum".to_string(),
                location: test_loc(),
            }),
            field: "Red".to_string(),
            location: test_loc(),
        };

        match field_access {
            Expr::FieldAccess { field, .. } => assert_eq!(field, "Red"),
            _ => panic!("Expected FieldAccess expression"),
        }
    }
}
