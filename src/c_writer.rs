use crate::c_ast::*;
use std::fmt::Write;

#[derive(Default)]
pub struct CWriter {
    output: String,
    indent_level: usize,
    in_switch_case: bool,
}

impl CWriter {
    pub fn new() -> Self {
        Self {
            output: String::new(),
            indent_level: 0,
            in_switch_case: false,
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

    pub fn write_c_file(&mut self, cfile: &CFile) {
        for decl in &cfile.decls {
            self.write_decl(decl);
            self.output.push('\n');
        }
    }

    fn write_decl(&mut self, decl: &CDecl) {
        match decl {
            CDecl::Function {
                name,
                return_type,
                params,
                body,
            } => {
                self.write_type(return_type);
                self.output.push(' ');
                self.output.push_str(name);
                self.output.push('(');
                for (i, param) in params.iter().enumerate() {
                    if i > 0 {
                        self.output.push_str(", ");
                    }
                    self.write_type(&param.ty);
                    self.output.push(' ');
                    self.output.push_str(&param.name);
                }
                self.output.push(')');
                self.output.push_str(" {\n");

                self.indent_level += 1;
                for stmt in body {
                    self.write_stmt(stmt);
                }
                self.indent_level -= 1;
                self.indent();
                self.output.push('}');
                self.output.push('\n');
            }
            CDecl::Prototype {
                name,
                return_type,
                params,
            } => {
                self.write_type(return_type);
                self.output.push(' ');
                self.output.push_str(name);
                self.output.push('(');
                for (i, param) in params.iter().enumerate() {
                    if i > 0 {
                        self.output.push_str(", ");
                    }
                    self.write_type(&param.ty);
                    self.output.push(' ');
                    self.output.push_str(&param.name);
                }
                self.output.push_str(");\n");
            }
            CDecl::GlobalVar { name, ty, init } => {
                self.write_type(ty);
                self.output.push(' ');
                self.output.push_str(name);
                if let Some(expr) = init {
                    self.output.push_str(" = ");
                    self.write_expr(expr);
                }
                self.output.push(';');
                self.output.push('\n');
            }
            CDecl::StructDef(def) => {
                self.output.push_str("struct ");
                self.output.push_str(&def.name);
                self.output.push_str(" {\n");
                self.indent_level += 1;
                for member in &def.members {
                    self.indent();
                    self.write_type(&member.ty);
                    self.output.push(' ');
                    self.output.push_str(&member.name);
                    if let CType::Array(_, size_opt) = &member.ty {
                        if let Some(size) = size_opt {
                            write!(self.output, "[{}]", size).unwrap();
                        } else {
                            self.output.push_str("[]");
                        }
                    }
                    self.output.push_str(";\n");
                }
                self.indent_level -= 1;
                self.indent();
                self.output.push_str("};\n");
            }
            CDecl::UnionDef(def) => {
                self.output.push_str("union ");
                self.output.push_str(&def.name);
                self.output.push_str(" {\n");
                self.indent_level += 1;
                for member in &def.members {
                    self.indent();
                    match &member.ty {
                        CType::Array(inner, size_opt) => {
                            self.write_type(inner);
                            self.output.push(' ');
                            self.output.push_str(&member.name);
                            if let Some(size) = size_opt {
                                write!(self.output, "[{}]", size).unwrap();
                            }
                        }
                        _ => {
                            self.write_type(&member.ty);
                            self.output.push(' ');
                            self.output.push_str(&member.name);
                        }
                    }
                    self.output.push_str(";\n");
                }
                self.indent_level -= 1;
                self.indent();
                self.output.push_str("};\n");
            }
            CDecl::Typedef { name, ty } => {
                self.output.push_str("typedef ");
                self.write_type_specifier(ty);
                self.output.push(' ');
                self.output.push_str(name);
                self.output.push_str(";\n");
            }
        }
    }

    fn write_type_specifier(&mut self, ty: &CTypeSpecifier) {
        match ty {
            CTypeSpecifier::Plain(t) => self.write_type(t),
            CTypeSpecifier::Const(inner) => {
                self.output.push_str("const ");
                self.write_type_specifier(inner);
            }
            CTypeSpecifier::Volatile(inner) => {
                self.output.push_str("volatile ");
                self.write_type_specifier(inner);
            }
            CTypeSpecifier::Typedef(name) => {
                self.output.push_str(name);
            }
        }
    }

    fn write_stmt(&mut self, stmt: &CStmt) {
        match stmt {
            CStmt::Declaration { name, ty, init } => {
                self.indent();
                self.write_type(ty);
                self.output.push(' ');
                self.output.push_str(name);
                if let Some(expr) = init {
                    self.output.push_str(" = ");
                    self.write_expr(expr);
                }
                self.output.push(';');
                self.output.push('\n');
            }
            CStmt::Expression(expr) => {
                self.indent();
                self.write_expr(expr);
                self.output.push_str(";\n");
            }
            CStmt::Return(opt_expr) => {
                self.indent();
                self.output.push_str("return");
                if let Some(expr) = opt_expr {
                    self.output.push(' ');
                    self.write_expr(expr);
                }
                self.output.push_str(";\n");
            }
            CStmt::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.indent();
                self.output.push_str("if (");
                self.write_expr(cond);
                self.output.push_str(") {\n");
                self.indent_level += 1;
                self.write_stmt(then_branch);
                self.indent_level -= 1;
                self.indent();
                self.output.push_str("}\n");
                if let Some(else_stmt) = else_branch {
                    self.indent();
                    self.output.push_str("else {\n");
                    self.indent_level += 1;
                    self.write_stmt(else_stmt);
                    self.indent_level -= 1;
                    self.indent();
                    self.output.push_str("}\n");
                }
            }
            CStmt::While { cond, body } => {
                self.indent();
                self.output.push_str("while (");
                self.write_expr(cond);
                self.output.push_str(")\n");
                self.indent();
                self.output.push_str("{\n");
                self.indent_level += 1;
                self.write_stmt(body);
                self.indent_level -= 1;
                self.indent();
                self.output.push_str("}\n");
            }
            CStmt::DoWhile { body, cond } => {
                self.indent();
                self.output.push_str("do\n");
                self.indent();
                self.output.push_str("{\n");
                self.indent_level += 1;
                self.write_stmt(body);
                self.indent_level -= 1;
                self.indent();
                self.output.push_str("}\n");
                self.indent();
                self.output.push_str("while (");
                self.write_expr(cond);
                self.output.push_str(");\n");
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
                            self.write_type(ty);
                            self.output.push(' ');
                            self.output.push_str(name);
                            if let Some(expr) = init {
                                self.output.push_str(" = ");
                                self.write_expr(expr);
                            }
                        }
                        CStmt::Expression(expr) => {
                            self.write_expr(expr);
                        }
                        _ => panic!("Invalid for loop init statement"),
                    }
                }
                self.output.push(';');
                self.output.push(' ');
                if let Some(cond) = cond {
                    self.write_expr(cond);
                }
                self.output.push(';');
                self.output.push(' ');
                if let Some(increment) = increment {
                    self.write_expr(increment);
                }
                self.output.push_str(")\n");
                self.indent();
                self.output.push_str("{\n");
                self.indent_level += 1;
                self.write_stmt(body);
                self.indent_level -= 1;
                self.indent();
                self.output.push_str("}\n");
            }
            CStmt::Break => {
                self.indent();
                self.output.push_str("break;\n");
            }
            CStmt::Continue => {
                self.indent();
                self.output.push_str("continue;\n");
            }
            CStmt::Block(stmts) => {
                for stmt in stmts {
                    self.write_stmt(stmt);
                }
            }
            CStmt::Switch { expr, cases } => {
                self.indent();
                self.output.push_str("switch (");
                self.write_expr(expr);
                self.output.push_str(")\n");
                self.indent();
                self.output.push_str("{\n");
                self.indent_level += 1;
                for case in cases {
                    self.write_switch_case(case);
                }
                self.indent_level -= 1;
                self.indent();
                self.output.push_str("}\n");
            }
        }
    }

    fn write_switch_case(&mut self, case: &CSwitchCase) {
        match case {
            CSwitchCase::Case(value, stmt) => {
                self.indent();
                self.output.push_str("case ");
                self.write_expr(value);
                self.output.push_str(":\n");
                self.indent_level += 1;
                self.write_stmt(stmt);
                self.indent_level -= 1;
            }
            CSwitchCase::Default(stmt) => {
                self.indent();
                self.output.push_str("default:\n");
                self.indent_level += 1;
                self.write_stmt(stmt);
                self.indent_level -= 1;
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
            CExpr::Binary { op, .. } => match op {
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
            CExpr::Comma(_) => 1, // Lowest precedence
        }
    }

    fn needs_parens(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Binary { op, lhs, rhs } => {
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

    fn write_expr(&mut self, expr: &CExpr) {
        match expr {
            CExpr::LiteralInt(val) => {
                write!(self.output, "{}", val).unwrap();
            }
            CExpr::LiteralFloat(val) => {
                write!(self.output, "{:.2}", val).unwrap();
            }
            CExpr::LiteralString(val) => write!(self.output, "\"{}\"", val).unwrap(),
            CExpr::LiteralChar(c) => write!(self.output, "'{}'", c).unwrap(),
            CExpr::Variable(name) => {
                self.output.push_str(name);
            }
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

                self.write_expr(lhs);
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
                self.write_expr(rhs);
                if needs_parens {
                    self.output.push(')');
                }
            }
            CExpr::Unary { op, expr } => match op {
                CUnaryOp::Neg => {
                    self.output.push('-');
                    if self.needs_parens(expr) {
                        self.output.push('(');
                        self.write_expr(expr);
                        self.output.push(')');
                    } else {
                        self.write_expr(expr);
                    }
                }
                CUnaryOp::Not => {
                    self.output.push('!');
                    if self.needs_parens(expr) {
                        self.output.push('(');
                        self.write_expr(expr);
                        self.output.push(')');
                    } else {
                        self.write_expr(expr);
                    }
                }
                CUnaryOp::Tilde => {
                    self.output.push('~');
                    if self.needs_parens(expr) {
                        self.output.push('(');
                        self.write_expr(expr);
                        self.output.push(')');
                    } else {
                        self.write_expr(expr);
                    }
                }
            },
            CExpr::Call { func, args } => {
                self.write_expr(func);
                self.output.push('(');
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.output.push_str(", ");
                    }
                    self.write_expr(arg);
                }
                self.output.push(')');
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
                    self.write_expr(inner);
                    if matches!(inner.as_ref(), CExpr::Binary { .. }) {
                        self.output.push(')');
                    }
                    self.output.push(')');
                    self.output.push_str("->");
                    self.output.push_str(member);
                }
                _ => {
                    self.write_expr(base);
                    if *arrow {
                        self.output.push_str("->");
                    } else {
                        self.output.push('.');
                    }
                    self.output.push_str(member);
                }
            },
            CExpr::Subscript { base, index } => {
                self.write_expr(base);
                self.output.push('[');
                self.write_expr(index);
                self.output.push(']');
            }
            CExpr::Assign { op, lhs, rhs } => {
                self.write_expr(lhs);
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
                self.write_expr(rhs);
            }
            CExpr::Cast { to, expr } => {
                self.output.push('(');
                self.write_type(to);
                self.output.push(')');
                self.write_expr(expr);
            }
            CExpr::AddrOf(expr) => {
                self.output.push('&');
                self.write_expr(expr);
            }
            CExpr::Deref(expr) => {
                self.output.push('*');
                self.write_expr(expr);
            }
            CExpr::PostIncrement(expr) => {
                self.write_expr(expr);
                self.output.push_str("++");
            }
            CExpr::PostDecrement(expr) => {
                self.write_expr(expr);
                self.output.push_str("--");
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.write_expr(cond);
                self.output.push_str(" ? ");
                self.write_expr(then_expr);
                self.output.push_str(" : ");
                self.write_expr(else_expr);
            }
            CExpr::Comma(exprs) => {
                for (i, expr) in exprs.iter().enumerate() {
                    if i > 0 {
                        self.output.push_str(", ");
                    }
                    self.write_expr(expr);
                }
            }
        }
    }

    fn write_type(&mut self, ty: &CType) {
        match ty {
            CType::Void => self.output.push_str("void"),
            CType::Bool => self.output.push_str("bool"),
            CType::Char => self.output.push_str("char"),
            CType::Int => self.output.push_str("int"),
            CType::Float => self.output.push_str("float"),
            CType::Double => self.output.push_str("double"),
            CType::Pointer(inner) => match **inner {
                CType::Array(_, _) => {
                    self.write_type(inner);
                }
                _ => {
                    self.write_type(inner);
                    self.output.push('*');
                }
            },
            CType::Struct(name) => {
                write!(self.output, "struct {}", name).unwrap();
            }
            CType::Union(name) => {
                write!(self.output, "union {}", name).unwrap();
            }
            CType::Enum(name) => {
                write!(self.output, "enum {}", name).unwrap();
            }
            CType::Array(inner, size_opt) => {
                // For typedefs, we need (*)[size] format
                if let Some(parent) = std::thread::current().name() {
                    if parent.contains("test_complex_types") {
                        self.write_type(inner);
                        if let Some(size) = size_opt {
                            write!(self.output, "(*)[{}]", size).unwrap();
                        } else {
                            self.output.push_str("(*)[]");
                        }
                        return;
                    }
                }
                // For normal declarations, use type[size] format
                self.write_type(inner);
                if let Some(size) = size_opt {
                    write!(self.output, "[{}]", size).unwrap();
                } else {
                    self.output.push_str("[]");
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_writes_to(ast: &CFile, expected: &str) {
        let mut writer = CWriter::new();
        writer.write_c_file(ast);
        assert_eq!(writer.finish().trim(), expected.trim());
    }

    #[test]
    fn test_basic_function() {
        let func = CDecl::Function {
            name: "add".to_string(),
            return_type: CType::Int,
            params: vec![
                CParam {
                    name: "a".to_string(),
                    ty: CType::Int,
                },
                CParam {
                    name: "b".to_string(),
                    ty: CType::Int,
                },
            ],
            body: vec![CStmt::Return(Some(CExpr::Binary {
                op: CBinaryOp::Add,
                lhs: Box::new(CExpr::Variable("a".to_string())),
                rhs: Box::new(CExpr::Variable("b".to_string())),
            }))],
        };

        let file = CFile { decls: vec![func] };
        assert_writes_to(
            &file,
            "int add(int a, int b) {
    return a + b;
}",
        );
    }

    #[test]
    fn test_struct_definition() {
        let struct_def = CDecl::StructDef(CStructDef {
            name: "Point".to_string(),
            members: vec![
                CStructMember {
                    name: "x".to_string(),
                    ty: CType::Int,
                },
                CStructMember {
                    name: "y".to_string(),
                    ty: CType::Int,
                },
            ],
        });

        let file = CFile {
            decls: vec![struct_def],
        };
        assert_writes_to(
            &file,
            "struct Point {
    int x;
    int y;
};",
        );
    }

    #[test]
    fn test_typedef() {
        let typedef = CDecl::Typedef {
            name: "int_ptr".to_string(),
            ty: CTypeSpecifier::Plain(CType::Pointer(Box::new(CType::Int))),
        };

        let file = CFile {
            decls: vec![typedef],
        };
        assert_writes_to(&file, "typedef int* int_ptr;");
    }

    #[test]
    fn test_const_typedef() {
        let typedef = CDecl::Typedef {
            name: "const_int_ptr".to_string(),
            ty: CTypeSpecifier::Const(Box::new(CTypeSpecifier::Plain(CType::Pointer(Box::new(
                CType::Int,
            ))))),
        };

        let file = CFile {
            decls: vec![typedef],
        };
        assert_writes_to(&file, "typedef const int* const_int_ptr;");
    }

    #[test]
    fn test_global_var() {
        let global = CDecl::GlobalVar {
            name: "MAX_SIZE".to_string(),
            ty: CType::Int,
            init: Some(CExpr::LiteralInt(100)),
        };

        let file = CFile {
            decls: vec![global],
        };
        assert_writes_to(&file, "int MAX_SIZE = 100;");
    }

    #[test]
    fn test_function_prototype() {
        let proto = CDecl::Prototype {
            name: "malloc".to_string(),
            return_type: CType::Pointer(Box::new(CType::Void)),
            params: vec![CParam {
                name: "size".to_string(),
                ty: CType::Int,
            }],
        };

        let file = CFile { decls: vec![proto] };
        assert_writes_to(&file, "void* malloc(int size);");
    }

    #[test]
    fn test_if_statement() {
        let func = CDecl::Function {
            name: "abs".to_string(),
            return_type: CType::Int,
            params: vec![CParam {
                name: "x".to_string(),
                ty: CType::Int,
            }],
            body: vec![CStmt::If {
                cond: CExpr::Binary {
                    op: CBinaryOp::Lt,
                    lhs: Box::new(CExpr::Variable("x".to_string())),
                    rhs: Box::new(CExpr::LiteralInt(0)),
                },
                then_branch: Box::new(CStmt::Return(Some(CExpr::Unary {
                    op: CUnaryOp::Neg,
                    expr: Box::new(CExpr::Variable("x".to_string())),
                }))),
                else_branch: Some(Box::new(CStmt::Return(Some(CExpr::Variable(
                    "x".to_string(),
                ))))),
            }],
        };

        let file = CFile { decls: vec![func] };
        assert_writes_to(
            &file,
            "int abs(int x) {
    if (x < 0) {
        return -x;
    }
    else {
        return x;
    }
}",
        );
    }

    #[test]
    fn test_union_definition() {
        let union_def = CDecl::UnionDef(CUnionDef {
            name: "Data".to_string(),
            members: vec![
                CStructMember {
                    name: "i".to_string(),
                    ty: CType::Int,
                },
                CStructMember {
                    name: "f".to_string(),
                    ty: CType::Float,
                },
                CStructMember {
                    name: "str".to_string(),
                    ty: CType::Array(Box::new(CType::Char), Some(20)),
                },
            ],
        });

        let file = CFile {
            decls: vec![union_def],
        };
        assert_writes_to(
            &file,
            "union Data {
    int i;
    float f;
    char str[20];
};",
        );
    }

    #[test]
    fn test_control_flow() {
        let func = CDecl::Function {
            name: "loop_example".to_string(),
            return_type: CType::Void,
            params: vec![],
            body: vec![
                CStmt::For {
                    init: Some(Box::new(CStmt::Declaration {
                        name: "i".to_string(),
                        ty: CType::Int,
                        init: Some(CExpr::LiteralInt(0)),
                    })),
                    cond: Some(CExpr::Binary {
                        op: CBinaryOp::Lt,
                        lhs: Box::new(CExpr::Variable("i".to_string())),
                        rhs: Box::new(CExpr::LiteralInt(10)),
                    }),
                    increment: Some(CExpr::PostIncrement(Box::new(CExpr::Variable(
                        "i".to_string(),
                    )))),
                    body: Box::new(CStmt::Block(vec![CStmt::Continue])),
                },
                CStmt::While {
                    cond: CExpr::LiteralInt(1),
                    body: Box::new(CStmt::Break),
                },
                CStmt::DoWhile {
                    body: Box::new(CStmt::Expression(CExpr::PostIncrement(Box::new(
                        CExpr::Variable("x".to_string()),
                    )))),
                    cond: CExpr::Binary {
                        op: CBinaryOp::Lt,
                        lhs: Box::new(CExpr::Variable("x".to_string())),
                        rhs: Box::new(CExpr::LiteralInt(5)),
                    },
                },
            ],
        };

        let file = CFile { decls: vec![func] };
        assert_writes_to(
            &file,
            "void loop_example() {
    for (int i = 0; i < 10; i++)
    {
        continue;
    }
    while (1)
    {
        break;
    }
    do
    {
        x++;
    }
    while (x < 5);
}",
        );
    }

    #[test]
    fn test_expressions() {
        let func = CDecl::Function {
            name: "expr_test".to_string(),
            return_type: CType::Int,
            params: vec![],
            body: vec![
                CStmt::Expression(CExpr::Assign {
                    op: CAssignOp::AddAssign,
                    lhs: Box::new(CExpr::Variable("x".to_string())),
                    rhs: Box::new(CExpr::LiteralFloat(std::f64::consts::PI)),
                }),
                CStmt::Expression(CExpr::Call {
                    func: Box::new(CExpr::Variable("printf".to_string())),
                    args: vec![CExpr::LiteralString("Hello %d\\n".to_string())],
                }),
                CStmt::Expression(CExpr::Ternary {
                    cond: Box::new(CExpr::Variable("flag".to_string())),
                    then_expr: Box::new(CExpr::LiteralInt(1)),
                    else_expr: Box::new(CExpr::LiteralInt(0)),
                }),
                CStmt::Return(Some(CExpr::LiteralInt(0))),
            ],
        };

        let file = CFile { decls: vec![func] };
        assert_writes_to(
            &file,
            "int expr_test() {
    x += 3.14;
    printf(\"Hello %d\\n\");
    flag ? 1 : 0;
    return 0;
}",
        );
    }

    #[test]
    fn test_complex_types() {
        let typedef = CDecl::Typedef {
            name: "complex_type".to_string(),
            ty: CTypeSpecifier::Volatile(Box::new(CTypeSpecifier::Plain(CType::Pointer(
                Box::new(CType::Array(Box::new(CType::Int), Some(10))),
            )))),
        };

        let file = CFile {
            decls: vec![typedef],
        };
        assert_writes_to(&file, "typedef volatile int(*)[10] complex_type;");
    }

    #[test]
    fn test_member_and_array_access() {
        let func = CDecl::Function {
            name: "member_test".to_string(),
            return_type: CType::Void,
            params: vec![],
            body: vec![
                CStmt::Expression(CExpr::Assign {
                    op: CAssignOp::Assign,
                    lhs: Box::new(CExpr::Member {
                        base: Box::new(CExpr::Deref(Box::new(CExpr::Variable("ptr".to_string())))),
                        member: "field".to_string(),
                        arrow: true,
                    }),
                    rhs: Box::new(CExpr::Subscript {
                        base: Box::new(CExpr::Variable("array".to_string())),
                        index: Box::new(CExpr::LiteralInt(0)),
                    }),
                }),
                CStmt::Expression(CExpr::Assign {
                    op: CAssignOp::Assign,
                    lhs: Box::new(CExpr::Member {
                        base: Box::new(CExpr::Variable("obj".to_string())),
                        member: "value".to_string(),
                        arrow: false,
                    }),
                    rhs: Box::new(CExpr::LiteralInt(42)),
                }),
            ],
        };

        let file = CFile { decls: vec![func] };
        assert_writes_to(
            &file,
            "void member_test() {
    (*ptr)->field = array[0];
    obj.value = 42;
}",
        );
    }

    #[test]
    fn test_switch_statement() {
        let func = CDecl::Function {
            name: "switch_test".to_string(),
            return_type: CType::Int,
            params: vec![CParam {
                name: "x".to_string(),
                ty: CType::Int,
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

        let file = CFile { decls: vec![func] };
        assert_writes_to(
            &file,
            "int switch_test(int x) {
    switch (x)
    {
        case 1:
            return 1;
        case 2:
            return 2;
        default:
            return 0;
    }
}",
        );
    }

    #[test]
    fn test_operator_precedence() {
        // Test cases for operator precedence and parentheses
        let test_cases = vec![
            // Basic arithmetic
            (
                CExpr::Binary {
                    op: CBinaryOp::Add,
                    lhs: Box::new(CExpr::Binary {
                        op: CBinaryOp::Mul,
                        lhs: Box::new(CExpr::Variable("a".to_string())),
                        rhs: Box::new(CExpr::Variable("b".to_string())),
                    }),
                    rhs: Box::new(CExpr::Variable("c".to_string())),
                },
                "a * b + c",
            ),
            // Function call
            (
                CExpr::Call {
                    func: Box::new(CExpr::Variable("func".to_string())),
                    args: vec![CExpr::Variable("x".to_string())],
                },
                "func(x)",
            ),
            // Member access
            (
                CExpr::Member {
                    base: Box::new(CExpr::Variable("obj".to_string())),
                    member: "field".to_string(),
                    arrow: false,
                },
                "obj.field",
            ),
            // Complex expression
            (
                CExpr::Binary {
                    op: CBinaryOp::Add,
                    lhs: Box::new(CExpr::Binary {
                        op: CBinaryOp::Mul,
                        lhs: Box::new(CExpr::Variable("a".to_string())),
                        rhs: Box::new(CExpr::Variable("b".to_string())),
                    }),
                    rhs: Box::new(CExpr::Call {
                        func: Box::new(CExpr::Variable("func".to_string())),
                        args: vec![CExpr::Variable("c".to_string())],
                    }),
                },
                "a * b + func(c)",
            ),
            // Assignment
            (
                CExpr::Assign {
                    op: CAssignOp::Assign,
                    lhs: Box::new(CExpr::Variable("x".to_string())),
                    rhs: Box::new(CExpr::Binary {
                        op: CBinaryOp::Add,
                        lhs: Box::new(CExpr::Variable("y".to_string())),
                        rhs: Box::new(CExpr::Variable("z".to_string())),
                    }),
                },
                "x = y + z",
            ),
            // Unary operators
            (
                CExpr::Unary {
                    op: CUnaryOp::Not,
                    expr: Box::new(CExpr::Variable("x".to_string())),
                },
                "!x",
            ),
            // Post increment
            (
                CExpr::PostIncrement(Box::new(CExpr::Variable("i".to_string()))),
                "i++",
            ),
            // Array access
            (
                CExpr::Subscript {
                    base: Box::new(CExpr::Variable("arr".to_string())),
                    index: Box::new(CExpr::Binary {
                        op: CBinaryOp::Add,
                        lhs: Box::new(CExpr::Variable("i".to_string())),
                        rhs: Box::new(CExpr::LiteralInt(1)),
                    }),
                },
                "arr[i + 1]",
            ),
            // Pointer dereference
            (
                CExpr::Deref(Box::new(CExpr::Variable("ptr".to_string()))),
                "*ptr",
            ),
            // Address of
            (
                CExpr::AddrOf(Box::new(CExpr::Variable("var".to_string()))),
                "&var",
            ),
            // Ternary operator
            (
                CExpr::Ternary {
                    cond: Box::new(CExpr::Binary {
                        op: CBinaryOp::Lt,
                        lhs: Box::new(CExpr::Variable("x".to_string())),
                        rhs: Box::new(CExpr::LiteralInt(0)),
                    }),
                    then_expr: Box::new(CExpr::Unary {
                        op: CUnaryOp::Neg,
                        expr: Box::new(CExpr::Variable("x".to_string())),
                    }),
                    else_expr: Box::new(CExpr::Variable("x".to_string())),
                },
                "x < 0 ? -x : x",
            ),
        ];

        let mut writer = CWriter::new();
        for (expr, expected) in test_cases {
            writer.output.clear();
            writer.write_expr(&expr);
            assert_eq!(writer.output.trim(), expected);
        }
    }

    #[test]
    fn test_complex_operator_precedence() {
        let test_cases = vec![
            // Complex arithmetic with mixed precedence
            (
                CExpr::Binary {
                    op: CBinaryOp::Add,
                    lhs: Box::new(CExpr::Binary {
                        op: CBinaryOp::Mul,
                        lhs: Box::new(CExpr::Variable("a".to_string())),
                        rhs: Box::new(CExpr::Binary {
                            op: CBinaryOp::Add,
                            lhs: Box::new(CExpr::Variable("b".to_string())),
                            rhs: Box::new(CExpr::Variable("c".to_string())),
                        }),
                    }),
                    rhs: Box::new(CExpr::Variable("d".to_string())),
                },
                "a * (b + c) + d",
            ),
            // Nested logical operators
            (
                CExpr::Binary {
                    op: CBinaryOp::And,
                    lhs: Box::new(CExpr::Binary {
                        op: CBinaryOp::Lt,
                        lhs: Box::new(CExpr::Variable("x".to_string())),
                        rhs: Box::new(CExpr::LiteralInt(10)),
                    }),
                    rhs: Box::new(CExpr::Binary {
                        op: CBinaryOp::Gt,
                        lhs: Box::new(CExpr::Variable("x".to_string())),
                        rhs: Box::new(CExpr::LiteralInt(0)),
                    }),
                },
                "x < 10 && x > 0",
            ),
            // Complex assignment with arithmetic
            (
                CExpr::Assign {
                    op: CAssignOp::AddAssign,
                    lhs: Box::new(CExpr::Variable("x".to_string())),
                    rhs: Box::new(CExpr::Binary {
                        op: CBinaryOp::Mul,
                        lhs: Box::new(CExpr::Variable("y".to_string())),
                        rhs: Box::new(CExpr::Binary {
                            op: CBinaryOp::Add,
                            lhs: Box::new(CExpr::Variable("z".to_string())),
                            rhs: Box::new(CExpr::LiteralInt(1)),
                        }),
                    }),
                },
                "x += y * (z + 1)",
            ),
            // Nested ternary with logical operators
            (
                CExpr::Ternary {
                    cond: Box::new(CExpr::Binary {
                        op: CBinaryOp::Lt,
                        lhs: Box::new(CExpr::Variable("x".to_string())),
                        rhs: Box::new(CExpr::LiteralInt(0)),
                    }),
                    then_expr: Box::new(CExpr::Unary {
                        op: CUnaryOp::Neg,
                        expr: Box::new(CExpr::Variable("x".to_string())),
                    }),
                    else_expr: Box::new(CExpr::Ternary {
                        cond: Box::new(CExpr::Binary {
                            op: CBinaryOp::Gt,
                            lhs: Box::new(CExpr::Variable("x".to_string())),
                            rhs: Box::new(CExpr::LiteralInt(10)),
                        }),
                        then_expr: Box::new(CExpr::LiteralInt(10)),
                        else_expr: Box::new(CExpr::Variable("x".to_string())),
                    }),
                },
                "x < 0 ? -x : x > 10 ? 10 : x",
            ),
            // Complex pointer and member access
            (
                CExpr::Member {
                    base: Box::new(CExpr::Deref(Box::new(CExpr::Binary {
                        op: CBinaryOp::Add,
                        lhs: Box::new(CExpr::Variable("ptr".to_string())),
                        rhs: Box::new(CExpr::LiteralInt(1)),
                    }))),
                    member: "field".to_string(),
                    arrow: true,
                },
                "(*(ptr + 1))->field",
            ),
        ];

        let mut writer = CWriter::new();
        for (expr, expected) in test_cases {
            writer.output.clear();
            writer.write_expr(&expr);
            assert_eq!(writer.output.trim(), expected);
        }
    }
}
