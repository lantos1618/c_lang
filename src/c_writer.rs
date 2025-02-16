use crate::c_ast::*;
use std::fmt::Write;

#[derive(Default)]
pub struct CWriter {
    output: String,
    indent_level: usize,
}

impl CWriter {
    pub fn new() -> Self {
        Self {
            output: String::new(),
            indent_level: 0,
        }
    }

    fn indent(&mut self) {
        for _ in 0..self.indent_level {
            self.output.push_str("    ");
        }
    }

    pub fn finish(self) -> String {
        self.output
    }

    pub fn write_c_file(&mut self, cfile: &CFile) -> std::fmt::Result {
        for decl in &cfile.decls {
            self.write_decl(decl)?;
            self.output.push('\n');
        }
        Ok(())
    }

    fn write_decl(&mut self, decl: &CDecl) -> std::fmt::Result {
        match decl {
            CDecl::Function {
                name,
                return_type,
                params,
                body,
            } => {
                self.write_type(return_type)?;
                write!(self.output, " {}(", name)?;
                self.write_params(params)?;
                self.output.push_str(") {\n");
                self.indent_level += 1;
                for stmt in body {
                    self.indent();
                    self.write_stmt(stmt)?;
                }
                self.indent_level -= 1;
                self.output.push_str("}\n");
                Ok(())
            }
            CDecl::Prototype {
                name,
                return_type,
                params,
            } => {
                self.write_type(return_type)?;
                write!(self.output, " {}(", name)?;
                self.write_params(params)?;
                self.output.push_str(");\n");
                Ok(())
            }
            CDecl::GlobalVar { name, ty, init } => {
                self.write_type(ty)?;
                write!(self.output, " {}", name)?;
                if let Some(init_expr) = init {
                    write!(self.output, " = ")?;
                    self.write_expr(init_expr)?;
                }
                self.output.push_str(";\n");
                Ok(())
            }
            CDecl::StructDef(def) => {
                write!(self.output, "struct {} {{\n", def.name)?;
                self.indent_level += 1;
                for member in &def.members {
                    self.indent();
                    self.write_type(&member.ty)?;
                    writeln!(self.output, " {};", member.name)?;
                }
                self.indent_level -= 1;
                self.output.push_str("};\n");
                Ok(())
            }
            CDecl::UnionDef(def) => {
                write!(self.output, "union {} {{\n", def.name)?;
                self.indent_level += 1;
                for member in &def.members {
                    self.indent();
                    self.write_type(&member.ty)?;
                    writeln!(self.output, " {};", member.name)?;
                }
                self.indent_level -= 1;
                self.output.push_str("};\n");
                Ok(())
            }
            CDecl::Typedef { name, ty } => {
                self.output.push_str("typedef ");
                self.write_type_specifier(ty)?;
                write!(self.output, " {};\n", name)?;
                Ok(())
            }
        }
    }

    fn write_params(&mut self, params: &[CParam]) -> std::fmt::Result {
        for (i, param) in params.iter().enumerate() {
            if i > 0 {
                self.output.push_str(", ");
            }
            self.write_type(&param.ty)?;
            write!(self.output, " {}", param.name)?;
        }
        Ok(())
    }

    fn write_stmt(&mut self, stmt: &CStmt) -> std::fmt::Result {
        match stmt {
            CStmt::Declaration { name, ty, init } => {
                self.write_type(ty)?;
                write!(self.output, " {}", name)?;
                if let Some(init_expr) = init {
                    write!(self.output, " = ")?;
                    self.write_expr(init_expr)?;
                }
                self.output.push_str(";\n");
                Ok(())
            }
            CStmt::Expression(expr) => {
                self.write_expr(expr)?;
                self.output.push_str(";\n");
                Ok(())
            }
            CStmt::Return(expr) => {
                self.output.push_str("return");
                if let Some(e) = expr {
                    write!(self.output, " ")?;
                    self.write_expr(e)?;
                }
                self.output.push_str(";\n");
                Ok(())
            }
            CStmt::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.output.push_str("if (");
                self.write_expr(cond)?;
                self.output.push_str(") {\n");
                self.indent_level += 1;
                self.indent();
                self.write_stmt(then_branch)?;
                self.indent_level -= 1;
                self.indent();
                self.output.push_str("}\n");
                if let Some(else_stmt) = else_branch {
                    self.indent();
                    self.output.push_str("else {\n");
                    self.indent_level += 1;
                    self.indent();
                    self.write_stmt(else_stmt)?;
                    self.indent_level -= 1;
                    self.indent();
                    self.output.push_str("}\n");
                }
                Ok(())
            }
            CStmt::While { cond, body } => {
                self.indent();
                self.output.push_str("while (");
                self.write_expr(cond)?;
                self.output.push_str(")\n");
                self.indent();
                self.output.push_str("{\n");
                self.indent_level += 1;
                self.write_stmt(body)?;
                self.indent_level -= 1;
                self.indent();
                self.output.push_str("}\n");
                Ok(())
            }
            CStmt::DoWhile { body, cond } => {
                self.indent();
                self.output.push_str("do\n");
                self.indent();
                self.output.push_str("{\n");
                self.indent_level += 1;
                self.write_stmt(body)?;
                self.indent_level -= 1;
                self.indent();
                self.output.push_str("}\n");
                self.indent();
                self.output.push_str("while (");
                self.write_expr(cond)?;
                self.output.push_str(");\n");
                Ok(())
            }
            CStmt::For {
                init,
                cond,
                increment,
                body,
            } => {
                self.indent();
                self.output.push_str("for (");
                if let Some(init_stmt) = init {
                    match &**init_stmt {
                        CStmt::Declaration { name, ty, init } => {
                            self.write_type(ty)?;
                            write!(self.output, " {}", name)?;
                            if let Some(expr) = init {
                                write!(self.output, " = ")?;
                                self.write_expr(expr)?;
                            }
                        }
                        CStmt::Expression(expr) => {
                            self.write_expr(expr)?;
                        }
                        _ => panic!("Invalid for loop init statement"),
                    }
                }
                self.output.push(';');
                self.output.push(' ');
                if let Some(cond) = cond {
                    self.write_expr(cond)?;
                }
                self.output.push(';');
                self.output.push(' ');
                if let Some(increment) = increment {
                    self.write_expr(increment)?;
                }
                self.output.push_str(")\n");
                self.indent();
                self.output.push_str("{\n");
                self.indent_level += 1;
                self.write_stmt(body)?;
                self.indent_level -= 1;
                self.indent();
                self.output.push_str("}\n");
                Ok(())
            }
            CStmt::Break => {
                self.indent();
                self.output.push_str("break;\n");
                Ok(())
            }
            CStmt::Continue => {
                self.indent();
                self.output.push_str("continue;\n");
                Ok(())
            }
            CStmt::Block(stmts) => {
                for stmt in stmts {
                    self.write_stmt(stmt)?;
                }
                Ok(())
            }
            CStmt::Switch { expr, cases } => {
                self.output.push_str("switch (");
                self.write_expr(expr)?;
                self.output.push_str(") {\n");
                for case in cases {
                    self.write_switch_case(case)?;
                }
                self.indent();
                self.output.push_str("}\n");
                Ok(())
            }
        }
    }

    fn write_switch_case(&mut self, case: &CSwitchCase) -> std::fmt::Result {
        match case {
            CSwitchCase::Case(value, stmt) => {
                self.indent();
                self.output.push_str("case ");
                self.write_expr(value)?;
                self.output.push_str(":\n");
                self.indent_level += 1;
                self.indent();
                self.write_stmt(stmt)?;
                self.indent_level -= 1;
                Ok(())
            }
            CSwitchCase::Default(stmt) => {
                self.indent();
                self.output.push_str("default:\n");
                self.indent_level += 1;
                self.indent();
                self.write_stmt(stmt)?;
                self.indent_level -= 1;
                Ok(())
            }
        }
    }

    fn get_precedence(&self, expr: &CExpr) -> i32 {
        match expr {
            CExpr::Variable(_) => 16, // Highest precedence
            CExpr::LiteralInt(_) => 16,
            CExpr::LiteralFloat(_) => 16,
            CExpr::LiteralString(_) => 16,
            CExpr::LiteralChar(_) => 16,
            CExpr::Call { .. } => 15,
            CExpr::Member { .. } => 15,
            CExpr::Subscript { .. } => 15,
            CExpr::PostIncrement(_) => 15,
            CExpr::PostDecrement(_) => 15,
            CExpr::Unary { op, .. } => match op {
                CUnaryOp::Neg | CUnaryOp::Not | CUnaryOp::Tilde => 14,
            },
            CExpr::Cast { .. } => 14,
            CExpr::AddrOf(_) => 14,
            CExpr::Deref(_) => 14,
            CExpr::Binary { op, lhs: _, rhs: _ } => match op {
                CBinaryOp::Mul | CBinaryOp::Div | CBinaryOp::Mod => 13,
                CBinaryOp::Add | CBinaryOp::Sub => 12,
                CBinaryOp::Shl | CBinaryOp::Shr => 11,
                CBinaryOp::Lt | CBinaryOp::Le | CBinaryOp::Gt | CBinaryOp::Ge => 10,
                CBinaryOp::Eq | CBinaryOp::Ne => 9,
                CBinaryOp::BitAnd => 8,
                CBinaryOp::BitXor => 7,
                CBinaryOp::BitOr => 6,
                CBinaryOp::And => 5,
                CBinaryOp::Or => 4,
            },
            CExpr::Ternary { .. } => 3,
            CExpr::Assign { .. } => 2,
            CExpr::Comma(_) => 1,
            CExpr::Block { .. } => 0, // Lowest precedence
        }
    }

    fn needs_parens(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Binary { op, lhs: _, rhs } => {
                let parent_precedence = self.get_precedence(expr);

                match rhs.as_ref() {
                    CExpr::Binary { op: child_op, .. } => {
                        let child_precedence = self.get_precedence(rhs);
                        child_precedence < parent_precedence
                            || (matches!(op, CBinaryOp::Mul)
                                && matches!(child_op, CBinaryOp::Add | CBinaryOp::Sub))
                    }
                    _ => false,
                }
            }
            CExpr::Unary { expr, .. } => {
                let expr_precedence = self.get_precedence(expr);
                let unary_precedence = 14; // Unary operators precedence
                expr_precedence < unary_precedence
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                let ternary_precedence = self.get_precedence(expr);
                let cond_precedence = self.get_precedence(cond);
                let then_precedence = self.get_precedence(then_expr);
                let else_precedence = self.get_precedence(else_expr);

                cond_precedence < ternary_precedence
                    || then_precedence < ternary_precedence
                    || else_precedence < ternary_precedence
            }
            CExpr::Deref(expr) => {
                // Special case for dereferencing a binary operation
                matches!(expr.as_ref(), CExpr::Binary { .. })
            }
            CExpr::Member { base, .. } => {
                // Only need parens for member access if base is a binary operation
                matches!(base.as_ref(), CExpr::Binary { .. })
            }
            CExpr::Subscript { base, index } => {
                // Only need parens for array access if base is a binary operation
                matches!(base.as_ref(), CExpr::Binary { .. })
                    || matches!(index.as_ref(), CExpr::Binary { .. })
            }
            _ => false, // Other expressions don't need parentheses by default
        }
    }

    fn write_expr(&mut self, expr: &CExpr) -> std::fmt::Result {
        match expr {
            CExpr::LiteralInt(i) => write!(self.output, "{}", i),
            CExpr::LiteralFloat(f) => write!(self.output, "{}", f),
            CExpr::LiteralString(s) => write!(self.output, "\"{}\"", s),
            CExpr::LiteralChar(c) => write!(self.output, "'{}'", c),
            CExpr::Variable(name) => write!(self.output, "{}", name),
            CExpr::Binary { op, lhs, rhs } => {
                let needs_parens = match rhs.as_ref() {
                    CExpr::Binary { op: rhs_op, .. } => {
                        let rhs_precedence = self.get_precedence(rhs);
                        let expr_precedence = self.get_precedence(expr);
                        rhs_precedence < expr_precedence
                            || (matches!(op, CBinaryOp::Mul)
                                && matches!(rhs_op, CBinaryOp::Add | CBinaryOp::Sub))
                    }
                    _ => false,
                };

                self.write_expr(lhs)?;
                self.output.push(' ');
                self.output.push_str(match op {
                    CBinaryOp::Add => "+",
                    CBinaryOp::Sub => "-",
                    CBinaryOp::Mul => "*",
                    CBinaryOp::Div => "/",
                    CBinaryOp::Mod => "%",
                    CBinaryOp::Lt => "<",
                    CBinaryOp::Le => "<=",
                    CBinaryOp::Gt => ">",
                    CBinaryOp::Ge => ">=",
                    CBinaryOp::Eq => "==",
                    CBinaryOp::Ne => "!=",
                    CBinaryOp::And => "&&",
                    CBinaryOp::Or => "||",
                    CBinaryOp::BitAnd => "&",
                    CBinaryOp::BitOr => "|",
                    CBinaryOp::BitXor => "^",
                    CBinaryOp::Shl => "<<",
                    CBinaryOp::Shr => ">>",
                });
                self.output.push(' ');
                if needs_parens {
                    self.output.push('(');
                }
                self.write_expr(rhs)?;
                if needs_parens {
                    self.output.push(')');
                }
                Ok(())
            }
            CExpr::Unary { op, expr } => match op {
                CUnaryOp::Neg => {
                    self.output.push('-');
                    if self.needs_parens(expr) {
                        self.output.push('(');
                        self.write_expr(expr)?;
                        self.output.push(')');
                    } else {
                        self.write_expr(expr)?;
                    }
                    Ok(())
                }
                CUnaryOp::Not => {
                    self.output.push('!');
                    if self.needs_parens(expr) {
                        self.output.push('(');
                        self.write_expr(expr)?;
                        self.output.push(')');
                    } else {
                        self.write_expr(expr)?;
                    }
                    Ok(())
                }
                CUnaryOp::Tilde => {
                    self.output.push('~');
                    if self.needs_parens(expr) {
                        self.output.push('(');
                        self.write_expr(expr)?;
                        self.output.push(')');
                    } else {
                        self.write_expr(expr)?;
                    }
                    Ok(())
                }
            },
            CExpr::Call { func, args } => {
                self.write_expr(func)?;
                self.output.push('(');
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.output.push_str(", ");
                    }
                    self.write_expr(arg)?;
                }
                self.output.push(')');
                Ok(())
            }
            CExpr::Member {
                base,
                member,
                arrow,
            } => match &**base {
                CExpr::Deref(inner) => {
                    self.output.push('(');
                    self.output.push('*');
                    if matches!(inner.as_ref(), CExpr::Binary { .. }) {
                        self.output.push('(');
                    }
                    self.write_expr(inner)?;
                    if matches!(inner.as_ref(), CExpr::Binary { .. }) {
                        self.output.push(')');
                    }
                    self.output.push(')');
                    self.output.push_str("->");
                    self.output.push_str(member);
                    Ok(())
                }
                _ => {
                    self.write_expr(base)?;
                    if *arrow {
                        self.output.push_str("->");
                    } else {
                        self.output.push('.');
                    }
                    self.output.push_str(member);
                    Ok(())
                }
            },
            CExpr::Subscript { base, index } => {
                self.write_expr(base)?;
                self.output.push('[');
                self.write_expr(index)?;
                self.output.push(']');
                Ok(())
            }
            CExpr::Assign { op, lhs, rhs } => {
                self.write_expr(lhs)?;
                self.output.push(' ');
                self.output.push_str(match op {
                    CAssignOp::Assign => "=",
                    CAssignOp::AddAssign => "+=",
                    CAssignOp::SubAssign => "-=",
                    CAssignOp::MulAssign => "*=",
                    CAssignOp::DivAssign => "/=",
                    CAssignOp::ModAssign => "%=",
                    CAssignOp::ShlAssign => "<<=",
                    CAssignOp::ShrAssign => ">>=",
                    CAssignOp::AndAssign => "&=",
                    CAssignOp::XorAssign => "^=",
                    CAssignOp::OrAssign => "|=",
                });
                self.output.push(' ');
                self.write_expr(rhs)?;
                Ok(())
            }
            CExpr::Cast { to, expr } => {
                self.output.push('(');
                self.write_type(to)?;
                self.output.push(')');
                self.write_expr(expr)?;
                Ok(())
            }
            CExpr::AddrOf(expr) => {
                self.output.push('&');
                self.write_expr(expr)?;
                Ok(())
            }
            CExpr::Deref(expr) => {
                self.output.push('*');
                self.write_expr(expr)?;
                Ok(())
            }
            CExpr::PostIncrement(expr) => {
                self.write_expr(expr)?;
                self.output.push_str("++");
                Ok(())
            }
            CExpr::PostDecrement(expr) => {
                self.write_expr(expr)?;
                self.output.push_str("--");
                Ok(())
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.write_expr(cond)?;
                self.output.push_str(" ? ");
                self.write_expr(then_expr)?;
                self.output.push_str(" : ");
                self.write_expr(else_expr)?;
                Ok(())
            }
            CExpr::Comma(exprs) => {
                for (i, expr) in exprs.iter().enumerate() {
                    if i > 0 {
                        self.output.push_str(", ");
                    }
                    self.write_expr(expr)?;
                }
                Ok(())
            }
            CExpr::Block { stmts, result } => {
                self.output.push('(');
                self.output.push('{');
                self.output.push('\n');
                self.indent_level += 1;

                for stmt in stmts {
                    self.indent();
                    self.write_stmt(stmt)?;
                }

                if let Some(result_expr) = result {
                    self.indent();
                    self.write_expr(result_expr)?;
                    self.output.push(';');
                    self.output.push('\n');
                }

                self.indent_level -= 1;
                self.indent();
                self.output.push('}');
                self.output.push(')');
                Ok(())
            }
        }
    }

    fn write_type(&mut self, ty: &CType) -> std::fmt::Result {
        match ty {
            CType::Void => {
                self.output.push_str("void");
                Ok(())
            }
            CType::Bool => {
                self.output.push_str("bool");
                Ok(())
            }
            CType::Char => {
                self.output.push_str("char");
                Ok(())
            }
            CType::Int8 => {
                self.output.push_str("int8_t");
                Ok(())
            }
            CType::Int16 => {
                self.output.push_str("int16_t");
                Ok(())
            }
            CType::Int32 => {
                self.output.push_str("int32_t");
                Ok(())
            }
            CType::Int64 => {
                self.output.push_str("int64_t");
                Ok(())
            }
            CType::IntPtr => {
                self.output.push_str("intptr_t");
                Ok(())
            }
            CType::UInt8 => {
                self.output.push_str("uint8_t");
                Ok(())
            }
            CType::UInt16 => {
                self.output.push_str("uint16_t");
                Ok(())
            }
            CType::UInt32 => {
                self.output.push_str("uint32_t");
                Ok(())
            }
            CType::UInt64 => {
                self.output.push_str("uint64_t");
                Ok(())
            }
            CType::UIntPtr => {
                self.output.push_str("uintptr_t");
                Ok(())
            }
            CType::Float => {
                self.output.push_str("float");
                Ok(())
            }
            CType::Double => {
                self.output.push_str("double");
                Ok(())
            }
            CType::Pointer(inner) => {
                self.write_type(inner)?;
                self.output.push('*');
                Ok(())
            }
            CType::Struct(name) => {
                self.output.push_str("struct ");
                self.output.push_str(name);
                Ok(())
            }
            CType::Union(name) => {
                self.output.push_str("union ");
                self.output.push_str(name);
                Ok(())
            }
            CType::Enum(name) => {
                self.output.push_str("enum ");
                self.output.push_str(name);
                Ok(())
            }
            CType::Array(inner, size) => {
                self.write_type(inner)?;
                self.output.push('[');
                if let Some(s) = size {
                    write!(self.output, "{}", s)?;
                }
                self.output.push(']');
                Ok(())
            }
        }
    }

    fn write_type_specifier(&mut self, spec: &CTypeSpecifier) -> std::fmt::Result {
        match spec {
            CTypeSpecifier::Plain(ty) => self.write_type(ty),
            CTypeSpecifier::Const(inner) => {
                self.output.push_str("const ");
                self.write_type_specifier(inner)
            }
            CTypeSpecifier::Volatile(inner) => {
                self.output.push_str("volatile ");
                self.write_type_specifier(inner)
            }
            CTypeSpecifier::Typedef(name) => {
                write!(self.output, "{}", name)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_write_function() -> std::fmt::Result {
        let mut writer = CWriter::new();
        let func = CDecl::Function {
            name: "add".to_string(),
            return_type: CType::Int32,
            params: vec![
                CParam {
                    name: "a".to_string(),
                    ty: CType::Int32,
                },
                CParam {
                    name: "b".to_string(),
                    ty: CType::Int32,
                },
            ],
            body: vec![CStmt::Return(Some(CExpr::Binary {
                op: CBinaryOp::Add,
                lhs: Box::new(CExpr::Variable("a".to_string())),
                rhs: Box::new(CExpr::Variable("b".to_string())),
            }))],
        };

        writer.write_decl(&func)?;
        assert_eq!(
            writer.output.trim(),
            "int32_t add(int32_t a, int32_t b) {\n    return a + b;\n}"
        );
        Ok(())
    }

    #[test]
    fn test_switch_statement() -> std::fmt::Result {
        let mut writer = CWriter::new();
        let func = CDecl::Function {
            name: "switch_test".to_string(),
            return_type: CType::Int32,
            params: vec![CParam {
                name: "x".to_string(),
                ty: CType::Int32,
            }],
            body: vec![CStmt::Switch {
                expr: CExpr::Variable("x".to_string()),
                cases: vec![
                    CSwitchCase::Case(
                        CExpr::LiteralInt(1),
                        Box::new(CStmt::Return(Some(CExpr::LiteralInt(1)))),
                    ),
                    CSwitchCase::Case(
                        CExpr::LiteralInt(2),
                        Box::new(CStmt::Return(Some(CExpr::LiteralInt(2)))),
                    ),
                    CSwitchCase::Default(Box::new(CStmt::Return(Some(CExpr::LiteralInt(0))))),
                ],
            }],
        };

        writer.write_decl(&func)?;
        assert_eq!(
            writer.output.trim(),
            "int32_t switch_test(int32_t x) {\n    switch (x) {\n    case 1:\n        return 1;\n    case 2:\n        return 2;\n    default:\n        return 0;\n    }\n}"
        );
        Ok(())
    }

    #[test]
    fn test_write_expressions() -> std::fmt::Result {
        let mut writer = CWriter::new();
        let test_cases = vec![
            (
                CExpr::Binary {
                    op: CBinaryOp::Add,
                    lhs: Box::new(CExpr::LiteralInt(1)),
                    rhs: Box::new(CExpr::LiteralInt(2)),
                },
                "1 + 2",
            ),
            (
                CExpr::Unary {
                    op: CUnaryOp::Not,
                    expr: Box::new(CExpr::Variable("x".to_string())),
                },
                "!x",
            ),
        ];

        for (expr, expected) in test_cases {
            writer.output.clear();
            writer.write_expr(&expr)?;
            assert_eq!(writer.output.trim(), expected);
        }
        Ok(())
    }
}
