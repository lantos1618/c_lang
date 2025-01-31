use crate::c_ast::*;
use std::fmt::Write;

pub struct CWriter {
    output: String,
    indent_level: usize,
}

impl CWriter {
    pub fn new() -> Self {
        CWriter {
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
                self.output.push_str("}\n");
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
                self.output.push_str(";\n");
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
                if let CType::Array(_, size_opt) = ty {
                    if let Some(size) = size_opt {
                        write!(self.output, "[{}]", size).unwrap();
                    } else {
                        self.output.push_str("[]");
                    }
                }
                if let Some(expr) = init {
                    self.output.push_str(" = ");
                    self.write_expr(expr);
                }
                self.output.push_str(";\n");
            }
            CStmt::Expression(expr) => {
                self.indent();
                self.write_expr(expr);
                self.output.push_str(";\n");
            }
            CStmt::Return(opt_expr) => {
                self.indent();
                self.output.push_str("return");
                if let Some(e) = opt_expr {
                    self.output.push(' ');
                    self.write_expr(e);
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
                self.output.push_str("}");
                if let Some(else_stmt) = else_branch {
                    self.output.push_str("\n");
                    self.indent();
                    self.output.push_str("else {\n");
                    self.indent_level += 1;
                    self.write_stmt(else_stmt);
                    self.indent_level -= 1;
                    self.indent();
                    self.output.push_str("}");
                }
                self.output.push('\n');
            }
            CStmt::While { cond, body } => {
                self.indent();
                self.output.push_str("while (");
                self.write_expr(cond);
                self.output.push_str(")\n");
                self.write_nested_stmt(body);
            }
            CStmt::DoWhile { body, cond } => {
                self.indent();
                self.output.push_str("do\n");
                self.write_nested_stmt(body);
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
                            if let Some(i) = init {
                                self.output.push_str(" = ");
                                self.write_expr(i);
                            }
                        }
                        CStmt::Expression(e) => {
                            self.write_expr(e);
                        }
                        _ => {
                            self.output.push_str("/* unsupported for-init */");
                        }
                    }
                }
                self.output.push_str("; ");
                if let Some(c) = cond {
                    self.write_expr(c);
                }
                self.output.push_str("; ");
                if let Some(inc) = increment {
                    self.write_expr(inc);
                }
                self.output.push_str(")\n");
                self.write_nested_stmt(body);
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
            CStmt::Break => {
                self.indent();
                self.output.push_str("break;\n");
            }
            CStmt::Continue => {
                self.indent();
                self.output.push_str("continue;\n");
            }
            CStmt::Block(stmts) => {
                self.indent();
                self.output.push_str("{\n");
                self.indent_level += 1;
                for s in stmts {
                    self.write_stmt(s);
                }
                self.indent_level -= 1;
                self.indent();
                self.output.push_str("}\n");
            }
        }
    }

    fn write_switch_case(&mut self, case: &CSwitchCase) {
        if let Some(val) = case.matches {
            self.indent();
            write!(self.output, "case {}:\n", val).unwrap();
        } else {
            self.indent();
            self.output.push_str("default:\n");
        }
        self.indent_level += 1;
        for stmt in &case.body {
            self.write_stmt(stmt);
        }
        self.indent_level -= 1;
    }

    fn write_nested_stmt(&mut self, stmt: &CStmt) {
        match stmt {
            CStmt::Block(_) => {
                self.write_stmt(stmt);
            }
            _ => {
                self.indent_level += 1;
                self.indent();
                self.output.push_str("{\n");
                self.indent_level += 1;
                self.write_stmt(stmt);
                self.indent_level -= 1;
                self.indent();
                self.output.push_str("}\n");
                self.indent_level -= 1;
            }
        }
    }

    fn write_expr(&mut self, expr: &CExpr) {
        match expr {
            CExpr::LiteralInt(i) => {
                write!(self.output, "{}", i).unwrap();
            }
            CExpr::LiteralFloat(f) => {
                write!(self.output, "{}", f).unwrap();
            }
            CExpr::LiteralString(s) => {
                write!(self.output, "\"{}\"", s).unwrap();
            }
            CExpr::LiteralChar(c) => {
                write!(self.output, "'{}'", c).unwrap();
            }
            CExpr::Variable(name) => {
                self.output.push_str(name);
            }
            CExpr::Unary { op, expr } => {
                match op {
                    CUnaryOp::Neg => self.output.push('('),
                    CUnaryOp::Not => self.output.push('!'),
                    CUnaryOp::Tilde => self.output.push('~'),
                }
                if matches!(op, CUnaryOp::Neg) {
                    self.output.push('-');
                }
                self.write_expr(expr);
                if matches!(op, CUnaryOp::Neg) {
                    self.output.push(')');
                }
            }
            CExpr::Binary { op, lhs, rhs } => {
                self.write_subexpr(lhs);
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
                self.write_subexpr(rhs);
            }
            CExpr::Assign { op, lhs, rhs } => {
                self.write_subexpr(lhs);
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
                self.write_subexpr(rhs);
            }
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
            CExpr::Cast { to, expr } => {
                self.output.push('(');
                self.write_type(to);
                self.output.push(')');
                self.write_subexpr(expr);
            }
            CExpr::AddrOf(e) => {
                self.output.push('&');
                self.write_subexpr(e);
            }
            CExpr::Deref(e) => {
                self.output.push('*');
                self.write_subexpr(e);
            }
            CExpr::PostIncrement(e) => {
                self.write_subexpr(e);
                self.output.push_str("++");
            }
            CExpr::PostDecrement(e) => {
                self.write_subexpr(e);
                self.output.push_str("--");
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.write_subexpr(cond);
                self.output.push_str(" ? ");
                self.write_subexpr(then_expr);
                self.output.push_str(" : ");
                self.write_subexpr(else_expr);
            }
            CExpr::Member {
                base,
                member,
                arrow,
            } => {
                self.write_subexpr(base);
                if *arrow {
                    self.output.push_str("->");
                } else {
                    self.output.push('.');
                }
                self.output.push_str(member);
            }
            CExpr::Subscript { base, index } => {
                self.write_subexpr(base);
                self.output.push('[');
                self.write_expr(index);
                self.output.push(']');
            }
            CExpr::Comma(exprs) => {
                for (i, e) in exprs.iter().enumerate() {
                    self.write_expr(e);
                    if i < exprs.len() - 1 {
                        self.output.push_str(", ");
                    }
                }
            }
        }
    }

    fn write_subexpr(&mut self, expr: &CExpr) {
        self.output.push('(');
        self.write_expr(expr);
        self.output.push(')');
    }

    fn write_type(&mut self, ty: &CType) {
        match ty {
            CType::Void => self.output.push_str("void"),
            CType::Bool => self.output.push_str("bool"),
            CType::Char => self.output.push_str("char"),
            CType::Int => self.output.push_str("int"),
            CType::Float => self.output.push_str("float"),
            CType::Double => self.output.push_str("double"),
            CType::Pointer(inner) => {
                self.write_type(inner);
                self.output.push('*');
            }
            CType::Struct(name) => {
                write!(self.output, "struct {}", name).unwrap();
            }
            CType::Union(name) => {
                write!(self.output, "union {}", name).unwrap();
            }
            CType::Enum(name) => {
                write!(self.output, "enum {}", name).unwrap();
            }
            CType::Array(inner, _) => {
                self.write_type(inner);
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
    return (a) + (b);
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
    if ((x) < (0)) {
        return (-x);
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
}
