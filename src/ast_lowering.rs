use crate::c_ast::*;
use crate::high_level_ast::*;

pub struct AstLowering {
    // State for the lowering process
    type_map: std::collections::HashMap<String, CType>,
}

impl AstLowering {
    pub fn new() -> Self {
        Self {
            type_map: std::collections::HashMap::new(),
        }
    }

    pub fn lower_module(&mut self, module: &Module) -> CFile {
        let mut decls = Vec::new();

        // First pass: collect all type definitions
        for decl in &module.decls {
            match decl {
                Decl::Struct(struct_def) => {
                    self.type_map.insert(
                        struct_def.name.clone(),
                        CType::Struct(struct_def.name.clone()),
                    );
                }
                Decl::Enum(enum_def) => {
                    self.type_map
                        .insert(enum_def.name.clone(), CType::Enum(enum_def.name.clone()));
                }
                Decl::Distinct(distinct_def) => {
                    let underlying = self.lower_type(&distinct_def.underlying_type);
                    self.type_map
                        .insert(distinct_def.name.clone(), underlying.clone());
                }
                _ => {}
            }
        }

        // Second pass: lower all declarations
        for decl in &module.decls {
            match decl {
                Decl::Function {
                    name,
                    params,
                    return_type,
                    body,
                } => {
                    decls.push(self.lower_function(name, params, return_type, body));
                }
                Decl::Struct(struct_def) => {
                    decls.push(self.lower_struct(struct_def));
                }
                Decl::Enum(enum_def) => {
                    decls.extend(self.lower_enum(enum_def));
                }
                Decl::Distinct(distinct_def) => {
                    decls.push(self.lower_distinct(distinct_def));
                }
            }
        }

        CFile { decls }
    }

    fn lower_type(&self, ty: &Type) -> CType {
        match ty {
            Type::Unit => CType::Void,
            Type::Bool => CType::Bool,
            Type::Int(size) => match size {
                IntSize::I8 => CType::Char, // For now, using char for i8
                _ => CType::Int,            // TODO: Add proper int sizes to CType
            },
            Type::UInt(_) => CType::Int, // TODO: Add unsigned types to CType
            Type::Float(size) => match size {
                FloatSize::F32 => CType::Float,
                FloatSize::F64 => CType::Double,
            },
            Type::String => CType::Pointer(Box::new(CType::Char)),
            Type::Array(inner, size) => CType::Array(Box::new(self.lower_type(inner)), *size),
            Type::Slice(inner) => CType::Pointer(Box::new(self.lower_type(inner))),
            Type::Pointer(inner) => CType::Pointer(Box::new(self.lower_type(inner))),
            Type::Reference(inner) => CType::Pointer(Box::new(self.lower_type(inner))),
            Type::Result(inner) => self.lower_type(inner), // TODO: Proper error handling
            Type::Struct(name) => self
                .type_map
                .get(name)
                .cloned()
                .unwrap_or(CType::Struct(name.clone())),
            Type::Enum(name) => self
                .type_map
                .get(name)
                .cloned()
                .unwrap_or(CType::Enum(name.clone())),
            Type::Distinct(name, _) => {
                self.type_map.get(name).cloned().unwrap_or(CType::Int) // Fallback to int if not found
            }
        }
    }

    fn lower_function(
        &self,
        name: &str,
        params: &[Parameter],
        return_type: &Type,
        body: &Option<Vec<Stmt>>,
    ) -> CDecl {
        let c_params = params
            .iter()
            .map(|p| CParam {
                name: p.name.clone(),
                ty: self.lower_type(&p.ty),
            })
            .collect();

        if let Some(body) = body {
            CDecl::Function {
                name: name.to_string(),
                return_type: self.lower_type(return_type),
                params: c_params,
                body: body.iter().map(|s| self.lower_stmt(s)).collect(),
            }
        } else {
            CDecl::Prototype {
                name: name.to_string(),
                return_type: self.lower_type(return_type),
                params: c_params,
            }
        }
    }

    fn lower_struct(&self, struct_def: &StructDef) -> CDecl {
        CDecl::StructDef(CStructDef {
            name: struct_def.name.clone(),
            members: struct_def
                .fields
                .iter()
                .map(|f| CStructMember {
                    name: f.name.clone(),
                    ty: self.lower_type(&f.ty),
                })
                .collect(),
        })
    }

    fn lower_enum(&self, enum_def: &EnumDef) -> Vec<CDecl> {
        let mut decls = Vec::new();

        // Create the enum type
        let enum_decl = CDecl::StructDef(CStructDef {
            name: enum_def.name.clone(),
            members: vec![
                CStructMember {
                    name: "tag".to_string(),
                    ty: CType::Int,
                },
                CStructMember {
                    name: "data".to_string(),
                    ty: CType::Union(format!("{}_Data", enum_def.name)),
                },
            ],
        });
        decls.push(enum_decl);

        // Create the union type for variant data
        let mut union_members = Vec::new();
        for variant in &enum_def.variants {
            if !variant.fields.is_empty() {
                union_members.push(CStructMember {
                    name: variant.name.to_lowercase(),
                    ty: CType::Struct(format!("{}_{}", enum_def.name, variant.name)),
                });
            }
        }

        let union_decl = CDecl::UnionDef(CUnionDef {
            name: format!("{}_Data", enum_def.name),
            members: union_members,
        });
        decls.push(union_decl);

        // Create structs for variants with data
        for variant in &enum_def.variants {
            if !variant.fields.is_empty() {
                let struct_decl = CDecl::StructDef(CStructDef {
                    name: format!("{}_{}", enum_def.name, variant.name),
                    members: variant
                        .fields
                        .iter()
                        .map(|f| CStructMember {
                            name: f.name.clone(),
                            ty: self.lower_type(&f.ty),
                        })
                        .collect(),
                });
                decls.push(struct_decl);
            }
        }

        decls
    }

    fn lower_distinct(&self, distinct_def: &DistinctDef) -> CDecl {
        CDecl::Typedef {
            name: distinct_def.name.clone(),
            ty: CTypeSpecifier::Plain(self.lower_type(&distinct_def.underlying_type)),
        }
    }

    fn lower_stmt(&self, stmt: &Stmt) -> CStmt {
        match stmt {
            Stmt::Let { name, ty, value } => CStmt::Declaration {
                name: name.clone(),
                ty: ty
                    .as_ref()
                    .map(|t| self.lower_type(t))
                    .unwrap_or(CType::Int), // Infer type from value
                init: Some(self.lower_expr(value)),
            },
            Stmt::Expr(expr) => CStmt::Expression(self.lower_expr(expr)),
            Stmt::Return(expr) => CStmt::Return(expr.as_ref().map(|e| self.lower_expr(e))),
            Stmt::Loop { body } => {
                let c_body = body.iter().map(|s| self.lower_stmt(s)).collect();
                CStmt::While {
                    cond: CExpr::LiteralInt(1), // while(1)
                    body: Box::new(CStmt::Block(c_body)),
                }
            }
            Stmt::While { cond, body } => {
                let c_body = body.iter().map(|s| self.lower_stmt(s)).collect();
                CStmt::While {
                    cond: self.lower_expr(cond),
                    body: Box::new(CStmt::Block(c_body)),
                }
            }
            Stmt::Break => CStmt::Break,
            Stmt::Continue => CStmt::Continue,
            Stmt::Block(stmts) => CStmt::Block(stmts.iter().map(|s| self.lower_stmt(s)).collect()),
        }
    }

    fn lower_expr(&self, expr: &Expr) -> CExpr {
        match expr {
            Expr::Literal(lit) => self.lower_literal(lit),
            Expr::Variable(name) => CExpr::Variable(name.clone()),
            Expr::Binary { op, left, right } => {
                let c_op = self.lower_binary_op(op);
                CExpr::Binary {
                    op: c_op,
                    lhs: Box::new(self.lower_expr(left)),
                    rhs: Box::new(self.lower_expr(right)),
                }
            }
            Expr::Unary { op, expr } => {
                let c_op = self.lower_unary_op(op);
                CExpr::Unary {
                    op: c_op,
                    expr: Box::new(self.lower_expr(expr)),
                }
            }
            Expr::Call { func, args } => CExpr::Call {
                func: Box::new(self.lower_expr(func)),
                args: args.iter().map(|a| self.lower_expr(a)).collect(),
            },
            Expr::FieldAccess { expr, field } => CExpr::Member {
                base: Box::new(self.lower_expr(expr)),
                member: field.clone(),
                arrow: matches!(**expr, Expr::Variable(_)), // Fixed: Properly dereference the boxed expression
            },
            Expr::ArrayAccess { array, index } => CExpr::Subscript {
                base: Box::new(self.lower_expr(array)),
                index: Box::new(self.lower_expr(index)),
            },
            Expr::Match { expr, arms } => self.lower_match(expr, arms),
        }
    }

    fn lower_literal(&self, lit: &Literal) -> CExpr {
        match lit {
            Literal::Int(i) => CExpr::LiteralInt(*i),
            Literal::Float(f) => CExpr::LiteralFloat(*f),
            Literal::String(s) => CExpr::LiteralString(s.clone()),
            Literal::Bool(b) => CExpr::LiteralInt(if *b { 1 } else { 0 }),
            Literal::Unit => CExpr::LiteralInt(0),
        }
    }

    fn lower_binary_op(&self, op: &BinaryOp) -> CBinaryOp {
        match op {
            BinaryOp::Add => CBinaryOp::Add,
            BinaryOp::Sub => CBinaryOp::Sub,
            BinaryOp::Mul => CBinaryOp::Mul,
            BinaryOp::Div => CBinaryOp::Div,
            BinaryOp::Mod => CBinaryOp::Mod,
            BinaryOp::And => CBinaryOp::And,
            BinaryOp::Or => CBinaryOp::Or,
            BinaryOp::Eq => CBinaryOp::Eq,
            BinaryOp::Ne => CBinaryOp::Ne,
            BinaryOp::Lt => CBinaryOp::Lt,
            BinaryOp::Le => CBinaryOp::Le,
            BinaryOp::Gt => CBinaryOp::Gt,
            BinaryOp::Ge => CBinaryOp::Ge,
        }
    }

    fn lower_unary_op(&self, op: &UnaryOp) -> CUnaryOp {
        match op {
            UnaryOp::Neg => CUnaryOp::Neg,
            UnaryOp::Not => CUnaryOp::Not,
        }
    }

    fn lower_match(&self, expr: &Expr, arms: &[MatchArm]) -> CExpr {
        // For now, convert match to a chain of ternary expressions
        // TODO: Use switch when possible
        let mut result = self.lower_default_match_arm();

        for arm in arms.iter().rev() {
            let condition = self.lower_pattern_check(expr, &arm.pattern);
            let body = self.lower_match_arm_body(&arm.body);

            result = CExpr::Ternary {
                cond: Box::new(condition),
                then_expr: Box::new(body),
                else_expr: Box::new(result),
            };
        }

        result
    }

    fn lower_pattern_check(&self, expr: &Expr, pattern: &Pattern) -> CExpr {
        match pattern {
            Pattern::Wildcard => CExpr::LiteralInt(1),
            Pattern::Literal(lit) => CExpr::Binary {
                op: CBinaryOp::Eq,
                lhs: Box::new(self.lower_expr(expr)),
                rhs: Box::new(self.lower_literal(lit)),
            },
            Pattern::Variable(_) => CExpr::LiteralInt(1),
            Pattern::EnumVariant { name, fields: _ } => CExpr::Binary {
                op: CBinaryOp::Eq,
                lhs: Box::new(CExpr::Member {
                    base: Box::new(self.lower_expr(expr)),
                    member: "tag".to_string(),
                    arrow: false,
                }),
                rhs: Box::new(CExpr::Variable(format!("{}_Tag", name))),
            },
            Pattern::Or(patterns) => {
                let mut result = self.lower_pattern_check(expr, &patterns[0]);
                for pattern in &patterns[1..] {
                    result = CExpr::Binary {
                        op: CBinaryOp::Or,
                        lhs: Box::new(result),
                        rhs: Box::new(self.lower_pattern_check(expr, pattern)),
                    };
                }
                result
            }
        }
    }

    fn lower_match_arm_body(&self, body: &[Stmt]) -> CExpr {
        // For now, just take the last expression or return a default value
        if let Some(Stmt::Expr(expr)) = body.last() {
            self.lower_expr(expr)
        } else {
            CExpr::LiteralInt(0)
        }
    }

    fn lower_default_match_arm(&self) -> CExpr {
        // TODO: Handle non-exhaustive matches
        CExpr::LiteralInt(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lower_simple_function() {
        let high_level = Module {
            decls: vec![Decl::Function {
                name: "add".to_string(),
                params: vec![
                    Parameter {
                        name: "a".to_string(),
                        ty: Type::Int(IntSize::I32),
                    },
                    Parameter {
                        name: "b".to_string(),
                        ty: Type::Int(IntSize::I32),
                    },
                ],
                return_type: Type::Int(IntSize::I32),
                body: Some(vec![Stmt::Return(Some(Expr::Binary {
                    op: BinaryOp::Add,
                    left: Box::new(Expr::Variable("a".to_string())),
                    right: Box::new(Expr::Variable("b".to_string())),
                }))]),
            }],
        };

        let mut lowering = AstLowering::new();
        let c_ast = lowering.lower_module(&high_level);

        assert_eq!(c_ast.decls.len(), 1);
        match &c_ast.decls[0] {
            CDecl::Function {
                name,
                return_type,
                params,
                body,
            } => {
                assert_eq!(name, "add");
                assert!(matches!(return_type, CType::Int));
                assert_eq!(params.len(), 2);
                assert_eq!(body.len(), 1);
            }
            _ => panic!("Expected function declaration"),
        }
    }

    #[test]
    fn test_lower_struct() {
        let high_level = Module {
            decls: vec![Decl::Struct(StructDef {
                name: "Point".to_string(),
                fields: vec![
                    Field {
                        name: "x".to_string(),
                        ty: Type::Float(FloatSize::F32),
                    },
                    Field {
                        name: "y".to_string(),
                        ty: Type::Float(FloatSize::F32),
                    },
                ],
            })],
        };

        let mut lowering = AstLowering::new();
        let c_ast = lowering.lower_module(&high_level);

        assert_eq!(c_ast.decls.len(), 1);
        match &c_ast.decls[0] {
            CDecl::StructDef(def) => {
                assert_eq!(def.name, "Point");
                assert_eq!(def.members.len(), 2);
                assert!(matches!(def.members[0].ty, CType::Float));
                assert!(matches!(def.members[1].ty, CType::Float));
            }
            _ => panic!("Expected struct definition"),
        }
    }
}
