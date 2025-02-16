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
}

#[derive(Debug, Clone)]
pub struct StructDef {
    pub name: String,
    pub fields: Vec<Field>,
}

#[derive(Debug, Clone)]
pub struct EnumVariant {
    pub name: String,
    pub fields: Vec<Field>,     // For variants with data
    pub value: Option<Literal>, // For explicit values like "RED"
}

#[derive(Debug, Clone)]
pub struct EnumDef {
    pub name: String,
    pub variants: Vec<EnumVariant>,
}

#[derive(Debug, Clone)]
pub struct DistinctDef {
    pub name: String,
    pub underlying_type: Type,
}

#[derive(Debug, Clone)]
pub struct Parameter {
    pub name: String,
    pub ty: Type,
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
    },
    Or(Vec<Pattern>), // Multiple patterns
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Vec<Stmt>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Literal(Literal),
    Variable(String),
    Binary {
        op: BinaryOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Unary {
        op: UnaryOp,
        expr: Box<Expr>,
    },
    Call {
        func: Box<Expr>,
        args: Vec<Expr>,
    },
    FieldAccess {
        expr: Box<Expr>,
        field: String,
    },
    ArrayAccess {
        array: Box<Expr>,
        index: Box<Expr>,
    },
    Match {
        expr: Box<Expr>,
        arms: Vec<MatchArm>,
    },
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Let {
        name: String,
        ty: Option<Type>, // Type inference if None
        value: Expr,
    },
    Expr(Expr),
    Return(Option<Expr>),
    Loop {
        body: Vec<Stmt>,
    },
    While {
        cond: Expr,
        body: Vec<Stmt>,
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
        body: Option<Vec<Stmt>>, // None for declarations, Some for definitions
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

    #[test]
    fn test_rgb_struct_definition() {
        let rgb_struct = StructDef {
            name: "RGB".to_string(),
            fields: vec![
                Field {
                    name: "R".to_string(),
                    ty: Type::UInt(IntSize::I8),
                },
                Field {
                    name: "G".to_string(),
                    ty: Type::UInt(IntSize::I8),
                },
                Field {
                    name: "B".to_string(),
                    ty: Type::UInt(IntSize::I8),
                },
            ],
        };

        assert_eq!(rgb_struct.name, "RGB");
        assert_eq!(rgb_struct.fields.len(), 3);
    }

    #[test]
    fn test_color_enum_definition() {
        let color_enum = EnumDef {
            name: "MyEnum".to_string(),
            variants: vec![
                EnumVariant {
                    name: "Red".to_string(),
                    fields: vec![],
                    value: Some(Literal::String("RED".to_string())),
                },
                EnumVariant {
                    name: "RGB".to_string(),
                    fields: vec![Field {
                        name: "rgb".to_string(),
                        ty: Type::Struct("RGB".to_string()),
                    }],
                    value: None,
                },
            ],
        };

        assert_eq!(color_enum.variants.len(), 2);
    }

    #[test]
    fn test_pattern_matching() {
        let match_stmt = Stmt::Expr(Expr::Match {
            expr: Box::new(Expr::Variable("col".to_string())),
            arms: vec![
                MatchArm {
                    pattern: Pattern::EnumVariant {
                        name: "Red".to_string(),
                        fields: vec![],
                    },
                    guard: None,
                    body: vec![
                        // Body statements for Red case
                    ],
                },
                MatchArm {
                    pattern: Pattern::EnumVariant {
                        name: "RGB".to_string(),
                        fields: vec![Pattern::Variable("rgb".to_string())],
                    },
                    guard: None,
                    body: vec![
                        // Body statements for RGB case
                    ],
                },
            ],
        });

        if let Stmt::Expr(Expr::Match { arms, .. }) = match_stmt {
            assert_eq!(arms.len(), 2);
        } else {
            panic!("Expected Match expression");
        }
    }

    #[test]
    fn test_function_definition() {
        let func = Decl::Function {
            name: "myFunc".to_string(),
            params: vec![Parameter {
                name: "a".to_string(),
                ty: Type::Int(IntSize::I32),
            }],
            return_type: Type::Result(Box::new(Type::Bool)),
            body: Some(vec![
                // Function body statements would go here
            ]),
        };

        if let Decl::Function {
            name,
            params,
            return_type,
            ..
        } = func
        {
            assert_eq!(name, "myFunc");
            assert_eq!(params.len(), 1);
            if let Type::Result(inner) = return_type {
                if let Type::Bool = *inner {
                    // Test passed
                } else {
                    panic!("Expected Bool as Result inner type");
                }
            } else {
                panic!("Expected Result type");
            }
        }
    }

    #[test]
    fn test_variable_assignment() {
        let assignment = Stmt::Let {
            name: "col".to_string(),
            ty: None, // Type inference
            value: Expr::FieldAccess {
                expr: Box::new(Expr::Variable("MyEnum".to_string())),
                field: "Red".to_string(),
            },
        };

        if let Stmt::Let { name, value, .. } = assignment {
            assert_eq!(name, "col");
            if let Expr::FieldAccess { field, .. } = value {
                assert_eq!(field, "Red");
            } else {
                panic!("Expected FieldAccess expression");
            }
        }
    }
}
