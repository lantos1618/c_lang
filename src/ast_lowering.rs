use crate::c_ast::*;
use crate::high_level_ast::*;

pub struct AstLowering {
    // State for the lowering process
    type_map: std::collections::HashMap<String, CType>,
}

#[derive(Debug, Clone)]
pub enum LoweringError {
    TypeNotFound(String),
    InvalidType(String),
    NonExhaustiveMatch(String),
    UnexpectedError(String),
}

impl AstLowering {
    pub fn new() -> Self {
        Self {
            type_map: std::collections::HashMap::new(),
        }
    }

    pub fn lower_module(&mut self, module: &Module) -> Result<CFile, LoweringError> {
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
                    let underlying = self.lower_type(&distinct_def.underlying_type)?;
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
                    decls.push(self.lower_function(name, params, return_type, body)?);
                }
                Decl::Struct(struct_def) => {
                    decls.push(self.lower_struct(struct_def)?);
                }
                Decl::Enum(enum_def) => {
                    decls.extend(self.lower_enum(enum_def)?);
                }
                Decl::Distinct(distinct_def) => {
                    decls.push(self.lower_distinct(distinct_def)?);
                }
            }
        }

        Ok(CFile { decls })
    }

    fn lower_type(&self, ty: &Type) -> Result<CType, LoweringError> {
        match ty {
            Type::Unit => Ok(CType::Void),
            Type::Bool => Ok(CType::Bool),
            Type::Int(size) => match size {
                IntSize::I8 => Ok(CType::Char),
                _ => Ok(CType::Int), // TODO: Add proper int sizes to CType
            },
            Type::UInt(_) => Ok(CType::Int), // TODO: Add unsigned types to CType
            Type::Float(size) => match size {
                FloatSize::F32 => Ok(CType::Float),
                FloatSize::F64 => Ok(CType::Double),
            },
            Type::String => Ok(CType::Pointer(Box::new(CType::Char))),
            Type::Array(inner, size) => Ok(CType::Array(Box::new(self.lower_type(inner)?), *size)),
            Type::Slice(inner) => Ok(CType::Pointer(Box::new(self.lower_type(inner)?))),
            Type::Pointer(inner) => Ok(CType::Pointer(Box::new(self.lower_type(inner)?))),
            Type::Reference(inner) => Ok(CType::Pointer(Box::new(self.lower_type(inner)?))),
            Type::Result(inner) => self.lower_type(inner), // TODO: Proper error handling
            Type::Struct(name) => {
                self.type_map.get(name).cloned().ok_or_else(|| {
                    LoweringError::TypeNotFound(format!("Struct {} not found", name))
                })
            }
            Type::Enum(name) => self
                .type_map
                .get(name)
                .cloned()
                .ok_or_else(|| LoweringError::TypeNotFound(format!("Enum {} not found", name))),
            Type::Distinct(name, _) => self.type_map.get(name).cloned().ok_or_else(|| {
                LoweringError::TypeNotFound(format!("Distinct type {} not found", name))
            }),
        }
    }

    fn lower_function(
        &self,
        name: &str,
        params: &[Parameter],
        return_type: &Type,
        body: &Option<Vec<Stmt>>,
    ) -> Result<CDecl, LoweringError> {
        let c_params = params
            .iter()
            .map(|p| -> Result<CParam, LoweringError> {
                Ok(CParam {
                    name: p.name.clone(),
                    ty: self.lower_type(&p.ty)?,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        let lowered_body = match body {
            Some(stmts) => {
                let mut c_stmts = Vec::new();
                for stmt in stmts {
                    c_stmts.push(self.lower_stmt(stmt)?);
                }
                c_stmts
            }
            None => Vec::new(),
        };

        Ok(if body.is_some() {
            CDecl::Function {
                name: name.to_string(),
                return_type: self.lower_type(return_type)?,
                params: c_params,
                body: lowered_body,
            }
        } else {
            CDecl::Prototype {
                name: name.to_string(),
                return_type: self.lower_type(return_type)?,
                params: c_params,
            }
        })
    }

    fn lower_struct(&self, struct_def: &StructDef) -> Result<CDecl, LoweringError> {
        let members = struct_def
            .fields
            .iter()
            .map(|f| -> Result<CStructMember, LoweringError> {
                Ok(CStructMember {
                    name: f.name.clone(),
                    ty: self.lower_type(&f.ty)?,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        Ok(CDecl::StructDef(CStructDef {
            name: struct_def.name.clone(),
            members,
        }))
    }

    fn lower_enum(&self, enum_def: &EnumDef) -> Result<Vec<CDecl>, LoweringError> {
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
                let members = variant
                    .fields
                    .iter()
                    .map(|f| -> Result<CStructMember, LoweringError> {
                        Ok(CStructMember {
                            name: f.name.clone(),
                            ty: self.lower_type(&f.ty)?,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                union_members.push(CStructMember {
                    name: variant.name.to_lowercase(),
                    ty: CType::Struct(format!("{}_{}", enum_def.name, variant.name)),
                });

                // Create struct for this variant
                decls.push(CDecl::StructDef(CStructDef {
                    name: format!("{}_{}", enum_def.name, variant.name),
                    members,
                }));
            }
        }

        let union_decl = CDecl::UnionDef(CUnionDef {
            name: format!("{}_Data", enum_def.name),
            members: union_members,
        });
        decls.push(union_decl);

        Ok(decls)
    }

    fn lower_distinct(&self, distinct_def: &DistinctDef) -> Result<CDecl, LoweringError> {
        Ok(CDecl::Typedef {
            name: distinct_def.name.clone(),
            ty: CTypeSpecifier::Plain(self.lower_type(&distinct_def.underlying_type)?),
        })
    }

    fn lower_stmt(&self, stmt: &Stmt) -> Result<CStmt, LoweringError> {
        match stmt {
            Stmt::Let { name, ty, value } => {
                let inferred_type = match ty {
                    Some(t) => self.lower_type(t)?,
                    None => {
                        return Err(LoweringError::InvalidType(
                            "Type inference not supported".to_string(),
                        ))
                    }
                };

                let init_expr = self.lower_expr(value)?;
                Ok(CStmt::Declaration {
                    name: name.clone(),
                    ty: inferred_type,
                    init: Some(init_expr),
                })
            }
            Stmt::Expr(expr) => {
                let lowered_expr = self.lower_expr(expr)?;
                Ok(CStmt::Expression(lowered_expr))
            }
            Stmt::Return(expr) => {
                let lowered_expr = match expr {
                    Some(e) => Some(self.lower_expr(e)?),
                    None => None,
                };
                Ok(CStmt::Return(lowered_expr))
            }
            Stmt::Loop { body } => {
                let mut c_body = Vec::new();
                for stmt in body {
                    c_body.push(self.lower_stmt(stmt)?);
                }

                Ok(CStmt::While {
                    cond: CExpr::LiteralInt(1),
                    body: Box::new(CStmt::Block(c_body)),
                })
            }
            Stmt::While { cond, body } => {
                let mut c_body = Vec::new();
                for stmt in body {
                    c_body.push(self.lower_stmt(stmt)?);
                }

                let lowered_cond = self.lower_expr(cond)?;
                Ok(CStmt::While {
                    cond: lowered_cond,
                    body: Box::new(CStmt::Block(c_body)),
                })
            }
            Stmt::Break => Ok(CStmt::Break),
            Stmt::Continue => Ok(CStmt::Continue),
            Stmt::Block(stmts) => {
                let mut c_stmts = Vec::new();
                for stmt in stmts {
                    c_stmts.push(self.lower_stmt(stmt)?);
                }
                Ok(CStmt::Block(c_stmts))
            }
        }
    }

    fn lower_expr(&self, expr: &Expr) -> Result<CExpr, LoweringError> {
        match expr {
            Expr::Literal(lit) => Ok(self.lower_literal(lit)),
            Expr::Variable(name) => Ok(CExpr::Variable(name.clone())),
            Expr::Binary { op, left, right } => {
                let c_op = self.lower_binary_op(op);
                Ok(CExpr::Binary {
                    op: c_op,
                    lhs: Box::new(self.lower_expr(left)?),
                    rhs: Box::new(self.lower_expr(right)?),
                })
            }
            Expr::Unary { op, expr } => {
                let c_op = self.lower_unary_op(op);
                Ok(CExpr::Unary {
                    op: c_op,
                    expr: Box::new(self.lower_expr(expr)?),
                })
            }
            Expr::Call { func, args } => {
                let lowered_args = args
                    .iter()
                    .map(|a| self.lower_expr(a))
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(CExpr::Call {
                    func: Box::new(self.lower_expr(func)?),
                    args: lowered_args,
                })
            }
            Expr::FieldAccess { expr, field } => Ok(CExpr::Member {
                base: Box::new(self.lower_expr(expr)?),
                member: field.clone(),
                arrow: matches!(**expr, Expr::Variable(_)),
            }),
            Expr::ArrayAccess { array, index } => Ok(CExpr::Subscript {
                base: Box::new(self.lower_expr(array)?),
                index: Box::new(self.lower_expr(index)?),
            }),
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

    fn lower_match(&self, expr: &Expr, arms: &[MatchArm]) -> Result<CExpr, LoweringError> {
        // Check if we can use a switch statement
        let can_use_switch = match expr {
            Expr::Variable(_) => true,
            Expr::FieldAccess { field: _, .. } => true,
            _ => false,
        };

        if !can_use_switch {
            return self.lower_match_to_ternary(expr, arms);
        }

        let switch_var = format!("__switch_{}", self.get_unique_id());
        let switch_expr = CExpr::Variable(switch_var.clone());

        let mut cases = Vec::new();
        let mut has_default = false;

        for arm in arms {
            match &arm.pattern {
                Pattern::Literal(lit) => {
                    let case_expr = self.lower_literal(lit);
                    let body = self.lower_match_arm_body(&arm.body)?;
                    cases.push(CSwitchCase::Case(
                        case_expr,
                        Box::new(CStmt::Block(vec![CStmt::Expression(body), CStmt::Break])),
                    ));
                }
                Pattern::EnumVariant { name, .. } => {
                    let case_expr = CExpr::Variable(format!("{}_Tag", name));
                    let body = self.lower_match_arm_body(&arm.body)?;
                    cases.push(CSwitchCase::Case(
                        case_expr,
                        Box::new(CStmt::Block(vec![CStmt::Expression(body), CStmt::Break])),
                    ));
                }
                Pattern::Wildcard => {
                    has_default = true;
                    let body = self.lower_match_arm_body(&arm.body)?;
                    cases.push(CSwitchCase::Default(Box::new(CStmt::Block(vec![
                        CStmt::Expression(body),
                        CStmt::Break,
                    ]))));
                }
                _ => {
                    return self.lower_match_to_ternary(expr, arms);
                }
            }
        }

        if !has_default {
            return Err(LoweringError::NonExhaustiveMatch(
                "Match expression is not exhaustive".to_string(),
            ));
        }

        Ok(CExpr::Block {
            stmts: vec![
                CStmt::Declaration {
                    name: switch_var.clone(),
                    ty: CType::Int, // TODO: Infer proper type
                    init: Some(self.lower_expr(expr)?),
                },
                CStmt::Switch {
                    expr: switch_expr,
                    cases,
                },
            ],
            result: Some(Box::new(CExpr::LiteralInt(0))), // TODO: Return proper value
        })
    }

    fn lower_match_to_ternary(
        &self,
        expr: &Expr,
        arms: &[MatchArm],
    ) -> Result<CExpr, LoweringError> {
        if arms.is_empty() {
            return Err(LoweringError::NonExhaustiveMatch(
                "Match expression has no arms".to_string(),
            ));
        }

        let mut has_wildcard = false;
        for arm in arms {
            if matches!(arm.pattern, Pattern::Wildcard) {
                has_wildcard = true;
                break;
            }
        }

        if !has_wildcard {
            return Err(LoweringError::NonExhaustiveMatch(
                "Match expression is not exhaustive - missing wildcard pattern".to_string(),
            ));
        }

        let mut result = self.lower_match_arm_body(&arms.last().unwrap().body)?;

        for arm in arms.iter().rev().skip(1) {
            let condition = self.lower_pattern_check(expr, &arm.pattern)?;
            let body = self.lower_match_arm_body(&arm.body)?;

            result = CExpr::Ternary {
                cond: Box::new(condition),
                then_expr: Box::new(body),
                else_expr: Box::new(result),
            };
        }

        Ok(result)
    }

    fn get_unique_id(&self) -> u32 {
        // TODO: Implement proper unique ID generation
        0
    }

    fn lower_pattern_check(&self, expr: &Expr, pattern: &Pattern) -> Result<CExpr, LoweringError> {
        match pattern {
            Pattern::Wildcard => Ok(CExpr::LiteralInt(1)),
            Pattern::Literal(lit) => Ok(CExpr::Binary {
                op: CBinaryOp::Eq,
                lhs: Box::new(self.lower_expr(expr)?),
                rhs: Box::new(self.lower_literal(lit)),
            }),
            Pattern::Variable(_) => Ok(CExpr::LiteralInt(1)),
            Pattern::EnumVariant { name, fields: _ } => Ok(CExpr::Binary {
                op: CBinaryOp::Eq,
                lhs: Box::new(CExpr::Member {
                    base: Box::new(self.lower_expr(expr)?),
                    member: "tag".to_string(),
                    arrow: false,
                }),
                rhs: Box::new(CExpr::Variable(format!("{}_Tag", name))),
            }),
            Pattern::Or(patterns) => {
                let mut result = self.lower_pattern_check(expr, &patterns[0])?;
                for pattern in &patterns[1..] {
                    result = CExpr::Binary {
                        op: CBinaryOp::Or,
                        lhs: Box::new(result),
                        rhs: Box::new(self.lower_pattern_check(expr, pattern)?),
                    };
                }
                Ok(result)
            }
        }
    }

    fn lower_match_arm_body(&self, body: &[Stmt]) -> Result<CExpr, LoweringError> {
        if body.is_empty() {
            return Err(LoweringError::UnexpectedError(
                "Match arm body is empty".to_string(),
            ));
        }

        match body.last() {
            Some(Stmt::Expr(expr)) => self.lower_expr(expr),
            Some(_) => Err(LoweringError::UnexpectedError(
                "Last statement in match arm must be an expression".to_string(),
            )),
            None => Err(LoweringError::UnexpectedError(
                "Match arm body is empty".to_string(),
            )),
        }
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
        let c_ast = lowering.lower_module(&high_level).unwrap();

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
        let c_ast = lowering.lower_module(&high_level).unwrap();

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
