`use crate::ast::*;
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
                self.output.push_str(")\n");
                self.write_nested_stmt(then_branch);
                if let Some(else_stmt) = else_branch {
                    self.indent();
                    self.output.push_str("else\n");
                    self.write_nested_stmt(else_stmt);
                }
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
                    CUnaryOp::Neg => self.output.push('-'),
                    CUnaryOp::Not => self.output.push('!'),
                    CUnaryOp::Tilde => self.output.push('~'),
                }
                self.write_subexpr(expr);
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
            CType::Array(inner, size_opt) => {
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
