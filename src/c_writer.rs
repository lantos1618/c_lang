use crate::c_ast::*;
use std::fmt::Write;

#[derive(Debug, Clone)]
pub struct FormattingOptions {
    pub indent_size: usize,
    pub use_tabs: bool,
    pub max_line_length: usize,
    pub brace_style: BraceStyle,
    pub space_after_control_flow_keyword: bool,
    pub space_around_operators: bool,
    pub space_after_comma: bool,
    pub wrap_long_lines: bool,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BraceStyle {
    SameLine,
    NextLine,
    NextLineIndented,
}

impl Default for FormattingOptions {
    fn default() -> Self {
        Self {
            indent_size: 4,
            use_tabs: false,
            max_line_length: 80,
            brace_style: BraceStyle::SameLine,
            space_after_control_flow_keyword: true,
            space_around_operators: true,
            space_after_comma: true,
            wrap_long_lines: true,
        }
    }
}

pub struct CWriter {
    output: String,
    indent_level: usize,
    options: FormattingOptions,
    current_line_length: usize,
}

impl Default for CWriter {
    fn default() -> Self {
        Self::new()
    }
}

impl CWriter {
    pub fn new() -> Self {
        Self::with_options(FormattingOptions::default())
    }

    pub fn with_options(options: FormattingOptions) -> Self {
        Self {
            output: String::with_capacity(1024), // Pre-allocate reasonable capacity
            indent_level: 0,
            options,
            current_line_length: 0,
        }
    }

    fn write_indent(&mut self) -> std::fmt::Result {
        self.current_line_length = self.indent_level * self.options.indent_size;
        if self.options.use_tabs {
            for _ in 0..self.indent_level {
                self.output.push('\t');
            }
        } else {
            for _ in 0..(self.indent_level * self.options.indent_size) {
                self.output.push(' ');
            }
        }
        Ok(())
    }

    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.current_line_length += s.len();
        self.output.push_str(s);
        Ok(())
    }

    fn write_char(&mut self, c: char) -> std::fmt::Result {
        self.current_line_length += 1;
        self.output.push(c);
        Ok(())
    }

    fn write_line(&mut self, s: &str) -> std::fmt::Result {
        self.write_indent()?;
        self.write_str(s)?;
        self.write_char('\n')?;
        self.current_line_length = 0;
        Ok(())
    }

    pub fn finish(self) -> String {
        self.output
    }

    pub fn write_c_file(&mut self, cfile: &CFile) -> std::fmt::Result {
        // Write includes first
        self.write_line("#include <stdbool.h>")?;
        self.write_line("#include <stdint.h>")?;
        self.write_line("#include <stdlib.h>")?;
        self.write_char('\n')?;

        for decl in &cfile.decls {
            self.write_decl(decl)?;
            self.write_char('\n')?;
        }
        Ok(())
    }

    fn should_wrap_line(&self, additional_length: usize) -> bool {
        if !self.options.wrap_long_lines {
            return false;
        }

        // Account for current indentation in line length calculation
        let effective_length = self.current_line_length + additional_length;
        let max_length = self.options.max_line_length;

        // More aggressive wrapping for function declarations and long expressions
        if effective_length > max_length {
            return true;
        }

        // For function declarations, wrap if we're close to the limit
        if effective_length > (max_length * 7 / 10) {
            // Changed from 8/10 to 7/10 for more aggressive wrapping
            // If we're already indented, this is likely a parameter list or complex expression
            if self.current_line_length > self.indent_level * self.options.indent_size {
                return true;
            }
        }

        false
    }

    fn estimate_content_length(&self, content: &str) -> usize {
        content.chars().count()
    }

    fn write_operator(&mut self, op: &str) -> std::fmt::Result {
        if self.options.space_around_operators {
            write!(self.output, " {} ", op)
        } else {
            write!(self.output, "{}", op)
        }
    }

    fn write_comma(&mut self) -> std::fmt::Result {
        if self.options.space_after_comma {
            write!(self.output, ", ")
        } else {
            write!(self.output, ",")
        }
    }

    fn write_params(&mut self, params: &[CParam]) -> std::fmt::Result {
        if params.is_empty() {
            return Ok(());
        }

        let mut first = true;
        for param in params {
            if !first {
                self.write_comma()?;
            }
            first = false;
            self.write_type(&param.ty)?;
            write!(self.output, " {}", param.name)?;
        }
        Ok(())
    }

    fn write_function_header(
        &mut self,
        name: &str,
        return_type: &CType,
        params: &[CParam],
    ) -> std::fmt::Result {
        self.write_type(return_type)?;
        write!(self.output, " {}(", name)?;

        // Simple rule: if we have multiple parameters or any parameter is long,
        // put each on its own line
        let should_wrap = params.len() > 1 || params.iter().any(|p| p.name.len() > 15);

        if should_wrap && !params.is_empty() {
            self.indent_level += 1;
            for (i, param) in params.iter().enumerate() {
                writeln!(self.output)?;
                self.write_indent()?;
                self.write_type(&param.ty)?;
                write!(self.output, " {}", param.name)?;
                if i < params.len() - 1 {
                    write!(self.output, ",")?;
                }
            }
            self.indent_level -= 1;
            writeln!(self.output)?;
            self.write_indent()?;
        } else {
            // For simple cases, keep everything on one line
            let mut first = true;
            for param in params {
                if !first {
                    self.write_comma()?;
                }
                first = false;
                self.write_type(&param.ty)?;
                write!(self.output, " {}", param.name)?;
            }
        }

        write!(self.output, ")")?;
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
                self.write_function_header(name, return_type, params)?;

                match self.options.brace_style {
                    BraceStyle::SameLine => self.write_str(" {\n")?,
                    BraceStyle::NextLine => {
                        self.write_char('\n')?;
                        self.write_str("{\n")?;
                    }
                    BraceStyle::NextLineIndented => {
                        self.write_char('\n')?;
                        self.write_indent()?;
                        self.write_str("{\n")?;
                    }
                }

                self.indent_level += 1;
                for stmt in body {
                    self.write_indent()?;
                    self.write_stmt(stmt)?;
                }
                self.indent_level -= 1;
                self.write_line("}")?;
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
                self.write_str(");\n")?;
                Ok(())
            }
            CDecl::GlobalVar { name, ty, init } => {
                self.write_type(ty)?;
                write!(self.output, " {}", name)?;
                if let Some(init_expr) = init {
                    write!(self.output, " = ")?;
                    self.write_expr(init_expr)?;
                }
                self.write_str(";\n")?;
                Ok(())
            }
            CDecl::StructDef(def) => {
                writeln!(self.output, "typedef struct {{")?;
                self.indent_level += 1;
                for member in &def.members {
                    self.write_indent()?;
                    self.write_type(&member.ty)?;
                    writeln!(self.output, " {};", member.name)?;
                }
                self.indent_level -= 1;
                writeln!(self.output, "}} {};", def.name)?;
                Ok(())
            }
            CDecl::UnionDef(def) => {
                writeln!(self.output, "typedef union {{")?;
                self.indent_level += 1;
                for member in &def.members {
                    self.write_indent()?;
                    self.write_type(&member.ty)?;
                    writeln!(self.output, " {};", member.name)?;
                }
                self.indent_level -= 1;
                writeln!(self.output, "}} {};", def.name)?;
                Ok(())
            }
            CDecl::Typedef { name, ty } => {
                write!(self.output, "typedef ")?;
                self.write_type_specifier(ty)?;
                writeln!(self.output, " {};", name)?;
                Ok(())
            }
        }
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
                writeln!(self.output, ";")?;
                Ok(())
            }
            CStmt::Expression(expr) => {
                self.write_expr(expr)?;
                writeln!(self.output, ";")?;
                Ok(())
            }
            CStmt::Return(expr) => {
                write!(self.output, "return")?;
                if let Some(e) = expr {
                    write!(self.output, " ")?;
                    self.write_expr(e)?;
                }
                writeln!(self.output, ";")?;
                Ok(())
            }
            CStmt::If {
                cond,
                then_branch,
                else_branch,
            } => {
                write!(self.output, "if (")?;
                self.write_expr(cond)?;
                write!(self.output, ") ")?;
                self.write_stmt(then_branch)?;
                if let Some(else_stmt) = else_branch {
                    write!(self.output, " else ")?;
                    self.write_stmt(else_stmt)?;
                }
                Ok(())
            }
            CStmt::While { cond, body } => {
                write!(self.output, "while (")?;
                self.write_expr(cond)?;
                write!(self.output, ") ")?;
                self.write_stmt(body)?;
                Ok(())
            }
            CStmt::DoWhile { body, cond } => {
                write!(self.output, "do ")?;
                self.write_stmt(body)?;
                write!(self.output, " while (")?;
                self.write_expr(cond)?;
                writeln!(self.output, ");")?;
                Ok(())
            }
            CStmt::For {
                init,
                cond,
                increment,
                body,
            } => {
                write!(self.output, "for (")?;
                if let Some(init_stmt) = init {
                    self.write_stmt(init_stmt)?;
                }
                write!(self.output, "; ")?;
                if let Some(cond_expr) = cond {
                    self.write_expr(cond_expr)?;
                }
                write!(self.output, "; ")?;
                if let Some(incr_expr) = increment {
                    self.write_expr(incr_expr)?;
                }
                write!(self.output, ") ")?;
                self.write_stmt(body)?;
                Ok(())
            }
            CStmt::Switch { expr, cases } => {
                write!(self.output, "switch (")?;
                self.write_expr(expr)?;
                writeln!(self.output, ") {{")?;
                self.indent_level += 1;
                for case in cases {
                    match case {
                        CSwitchCase::Case(expr, stmt) => {
                            self.write_indent()?;
                            write!(self.output, "case ")?;
                            self.write_expr(expr)?;
                            writeln!(self.output, ":")?;
                            self.indent_level += 1;
                            self.write_indent()?;
                            self.write_stmt(stmt)?;
                            self.indent_level -= 1;
                        }
                        CSwitchCase::Default(stmt) => {
                            self.write_indent()?;
                            writeln!(self.output, "default:")?;
                            self.indent_level += 1;
                            self.write_indent()?;
                            self.write_stmt(stmt)?;
                            self.indent_level -= 1;
                        }
                    }
                }
                self.indent_level -= 1;
                self.write_indent()?;
                writeln!(self.output, "}}")?;
                Ok(())
            }
            CStmt::Break => {
                writeln!(self.output, "break;")?;
                Ok(())
            }
            CStmt::Continue => {
                writeln!(self.output, "continue;")?;
                Ok(())
            }
            CStmt::Block(stmts) => {
                writeln!(self.output, "{{")?;
                self.indent_level += 1;
                for stmt in stmts {
                    self.write_indent()?;
                    self.write_stmt(stmt)?;
                }
                self.indent_level -= 1;
                self.write_indent()?;
                writeln!(self.output, "}}")?;
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

    fn write_binary_expr(
        &mut self,
        op: &CBinaryOp,
        lhs: &CExpr,
        rhs: &CExpr,
        needs_parens: bool,
    ) -> std::fmt::Result {
        if needs_parens {
            write!(self.output, "(")?;
        }

        let op_str = match op {
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
        };

        // Estimate the length of the expression
        let mut expr_str = String::new();
        write!(expr_str, "{:?}", lhs)?;
        write!(expr_str, " {} ", op_str)?;
        write!(expr_str, "{:?}", rhs)?;

        let should_wrap = self.should_wrap_line(self.estimate_content_length(&expr_str));

        // For nested binary expressions, we need special handling
        if let CExpr::Binary {
            op: inner_op,
            lhs: inner_lhs,
            rhs: inner_rhs,
        } = lhs
        {
            // Write the inner binary expression
            self.write_binary_expr(inner_op, inner_lhs, inner_rhs, false)?;

            // For assignment statements, always wrap after the operator
            let in_assignment = matches!(inner_op, CBinaryOp::Add) && matches!(op, CBinaryOp::Add);
            if in_assignment {
                self.write_operator(op_str)?;
                writeln!(self.output)?;
                self.write_indent()?;
            } else {
                self.write_operator(op_str)?;
            }

            self.write_expr(rhs)?;
        } else {
            // For non-nested expressions, write normally
            self.write_expr(lhs)?;
            self.write_operator(op_str)?;

            if should_wrap && !matches!(rhs, CExpr::Binary { .. }) {
                writeln!(self.output)?;
                self.write_indent()?;
            }

            self.write_expr(rhs)?;
        }

        if needs_parens {
            write!(self.output, ")")?;
        }
        Ok(())
    }

    fn write_expr(&mut self, expr: &CExpr) -> std::fmt::Result {
        match expr {
            CExpr::LiteralInt(i) => write!(self.output, "{}", i),
            CExpr::LiteralFloat(f) => write!(self.output, "{}", f),
            CExpr::LiteralString(s) => write!(self.output, "\"{}\"", s),
            CExpr::LiteralChar(c) => write!(self.output, "'{}'", c),
            CExpr::Variable(name) => write!(self.output, "{}", name),
            CExpr::Unary { op, expr } => {
                write!(
                    self.output,
                    "{}",
                    match op {
                        CUnaryOp::Neg => "-",
                        CUnaryOp::Not => "!",
                        CUnaryOp::Tilde => "~",
                    }
                )?;
                if self.needs_parens(expr) {
                    write!(self.output, "(")?;
                    self.write_expr(expr)?;
                    write!(self.output, ")")?;
                } else {
                    self.write_expr(expr)?;
                }
                Ok(())
            }
            CExpr::Binary { op, lhs, rhs } => {
                self.write_binary_expr(op, lhs, rhs, self.needs_parens(expr))
            }
            CExpr::Assign { op, lhs, rhs } => {
                self.write_expr(lhs)?;
                let op_str = match op {
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
                };

                write!(self.output, " {} ", op_str)?;

                // Special handling for binary expressions in assignments
                if let CExpr::Binary {
                    op: bin_op,
                    lhs: bin_lhs,
                    rhs: bin_rhs,
                } = rhs.as_ref()
                {
                    // For nested binary expressions in assignments, we need special handling
                    if let CExpr::Binary {
                        op: inner_op,
                        lhs: inner_lhs,
                        rhs: inner_rhs,
                    } = bin_lhs.as_ref()
                    {
                        // Write the first part of the inner binary expression
                        self.write_expr(inner_lhs)?;
                        write!(
                            self.output,
                            " {}",
                            match inner_op {
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
                            }
                        )?;
                        write!(self.output, " ")?;
                        self.write_expr(inner_rhs)?;
                        write!(
                            self.output,
                            " {}",
                            match bin_op {
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
                            }
                        )?;
                        writeln!(self.output)?;
                        self.write_indent()?;
                        self.write_expr(bin_rhs)?;
                    } else {
                        // Write the first part of the binary expression
                        self.write_expr(bin_lhs)?;
                        write!(
                            self.output,
                            " {}",
                            match bin_op {
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
                            }
                        )?;
                        writeln!(self.output)?;
                        self.write_indent()?;
                        self.write_expr(bin_rhs)?;
                    }
                } else {
                    self.write_expr(rhs)?;
                }
                Ok(())
            }
            CExpr::Call { func, args } => {
                self.write_expr(func)?;
                write!(self.output, "(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(self.output, ", ")?;
                    }
                    self.write_expr(arg)?;
                }
                write!(self.output, ")")?;
                Ok(())
            }
            CExpr::Cast { to, expr } => {
                write!(self.output, "(")?;
                self.write_type(to)?;
                write!(self.output, ")")?;
                if self.needs_parens(expr) {
                    write!(self.output, "(")?;
                    self.write_expr(expr)?;
                    write!(self.output, ")")?;
                } else {
                    self.write_expr(expr)?;
                }
                Ok(())
            }
            CExpr::AddrOf(expr) => {
                write!(self.output, "&")?;
                if self.needs_parens(expr) {
                    write!(self.output, "(")?;
                    self.write_expr(expr)?;
                    write!(self.output, ")")?;
                } else {
                    self.write_expr(expr)?;
                }
                Ok(())
            }
            CExpr::Deref(expr) => {
                write!(self.output, "*")?;
                if self.needs_parens(expr) {
                    write!(self.output, "(")?;
                    self.write_expr(expr)?;
                    write!(self.output, ")")?;
                } else {
                    self.write_expr(expr)?;
                }
                Ok(())
            }
            CExpr::PostIncrement(expr) => {
                self.write_expr(expr)?;
                write!(self.output, "++")?;
                Ok(())
            }
            CExpr::PostDecrement(expr) => {
                self.write_expr(expr)?;
                write!(self.output, "--")?;
                Ok(())
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                if self.needs_parens(expr) {
                    write!(self.output, "(")?;
                }
                self.write_expr(cond)?;
                write!(self.output, " ? ")?;
                self.write_expr(then_expr)?;
                write!(self.output, " : ")?;
                self.write_expr(else_expr)?;
                if self.needs_parens(expr) {
                    write!(self.output, ")")?;
                }
                Ok(())
            }
            CExpr::Member {
                base,
                member,
                arrow,
            } => {
                if self.needs_parens(base) {
                    write!(self.output, "(")?;
                    self.write_expr(base)?;
                    write!(self.output, ")")?;
                } else {
                    self.write_expr(base)?;
                }
                write!(self.output, "{}{}", if *arrow { "->" } else { "." }, member)?;
                Ok(())
            }
            CExpr::Subscript { base, index } => {
                if self.needs_parens(base) {
                    write!(self.output, "(")?;
                    self.write_expr(base)?;
                    write!(self.output, ")")?;
                } else {
                    self.write_expr(base)?;
                }
                write!(self.output, "[")?;
                self.write_expr(index)?;
                write!(self.output, "]")?;
                Ok(())
            }
            CExpr::Comma(exprs) => {
                write!(self.output, "(")?;
                for (i, expr) in exprs.iter().enumerate() {
                    if i > 0 {
                        write!(self.output, ", ")?;
                    }
                    self.write_expr(expr)?;
                }
                write!(self.output, ")")?;
                Ok(())
            }
            CExpr::Block { stmts, result } => {
                writeln!(self.output, "{{")?;
                self.indent_level += 1;
                for stmt in stmts {
                    self.write_indent()?;
                    self.write_stmt(stmt)?;
                }
                if let Some(result_expr) = result {
                    self.write_indent()?;
                    self.write_expr(result_expr)?;
                    writeln!(self.output)?;
                }
                self.indent_level -= 1;
                self.write_indent()?;
                write!(self.output, "}}")?;
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
                self.output.push_str("signed char"); // More standard C
                Ok(())
            }
            CType::Int16 => {
                self.output.push_str("short"); // More standard C
                Ok(())
            }
            CType::Int32 => {
                self.output.push_str("int"); // More standard C
                Ok(())
            }
            CType::Int64 => {
                self.output.push_str("long long"); // More standard C
                Ok(())
            }
            CType::IntPtr => {
                self.output.push_str("intptr_t"); // Keep this as is since it's platform-specific
                Ok(())
            }
            CType::UInt8 => {
                self.output.push_str("unsigned char"); // More standard C
                Ok(())
            }
            CType::UInt16 => {
                self.output.push_str("unsigned short"); // More standard C
                Ok(())
            }
            CType::UInt32 => {
                self.output.push_str("unsigned int"); // More standard C
                Ok(())
            }
            CType::UInt64 => {
                self.output.push_str("unsigned long long"); // More standard C
                Ok(())
            }
            CType::UIntPtr => {
                self.output.push_str("uintptr_t"); // Keep this as is since it's platform-specific
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
                write!(self.output, "{}", name)?; // Remove 'struct' prefix since we're using typedef
                Ok(())
            }
            CType::Union(name) => {
                write!(self.output, "{}", name)?; // Remove 'union' prefix since we're using typedef
                Ok(())
            }
            CType::Enum(name) => {
                write!(self.output, "{}", name)?; // Remove 'enum' prefix since we're using typedef
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
    fn test_basic_formatting() {
        let mut writer = CWriter::new();
        let program = CFile {
            decls: vec![CDecl::Function {
                name: "test".to_string(),
                return_type: CType::Int32,
                params: vec![],
                body: vec![
                    CStmt::Declaration {
                        name: "x".to_string(),
                        ty: CType::Int32,
                        init: Some(CExpr::LiteralInt(42)),
                    },
                    CStmt::Return(Some(CExpr::Variable("x".to_string()))),
                ],
            }],
        };

        writer.write_c_file(&program).unwrap();
        let output = writer.finish();
        assert!(output.contains("int test()"));
        assert!(output.contains("int x = 42;"));
        assert!(output.contains("return x;"));
    }

    #[test]
    fn test_formatting_options() {
        let options = FormattingOptions {
            indent_size: 2,
            use_tabs: false,
            max_line_length: 80,
            brace_style: BraceStyle::NextLine,
            space_after_control_flow_keyword: true,
            space_around_operators: true,
            space_after_comma: true,
            wrap_long_lines: true,
        };
        let mut writer = CWriter::with_options(options);
        let program = CFile {
            decls: vec![CDecl::Function {
                name: "test".to_string(),
                return_type: CType::Int32,
                params: vec![],
                body: vec![CStmt::If {
                    cond: CExpr::LiteralInt(1),
                    then_branch: Box::new(CStmt::Return(Some(CExpr::LiteralInt(1)))),
                    else_branch: Some(Box::new(CStmt::Return(Some(CExpr::LiteralInt(0))))),
                }],
            }],
        };

        writer.write_c_file(&program).unwrap();
        let output = writer.finish();
        assert!(output.contains("  if")); // Check indent size
        assert!(output.contains("int test()\n{")); // Check brace style
    }

    #[test]
    fn test_complex_expressions() {
        let mut writer = CWriter::new();
        let expr = CExpr::Binary {
            op: CBinaryOp::Add,
            lhs: Box::new(CExpr::Binary {
                op: CBinaryOp::Mul,
                lhs: Box::new(CExpr::LiteralInt(2)),
                rhs: Box::new(CExpr::LiteralInt(3)),
            }),
            rhs: Box::new(CExpr::LiteralInt(4)),
        };

        writer.write_expr(&expr).unwrap();
        let output = writer.finish();
        assert_eq!(output, "2 * 3 + 4");
    }

    #[test]
    fn test_struct_formatting() {
        let mut writer = CWriter::new();
        let program = CFile {
            decls: vec![CDecl::StructDef(CStructDef {
                name: "Point".to_string(),
                members: vec![
                    CStructMember {
                        name: "x".to_string(),
                        ty: CType::Float,
                    },
                    CStructMember {
                        name: "y".to_string(),
                        ty: CType::Float,
                    },
                ],
            })],
        };

        writer.write_c_file(&program).unwrap();
        let output = writer.finish();
        assert!(output.contains("typedef struct {"));
        assert!(output.contains("float x;"));
        assert!(output.contains("float y;"));
        assert!(output.contains("} Point;"));
    }

    #[test]
    fn test_integer_types() {
        let mut writer = CWriter::new();
        let program = CFile {
            decls: vec![CDecl::Function {
                name: "test_types".to_string(),
                return_type: CType::Void,
                params: vec![],
                body: vec![
                    CStmt::Declaration {
                        name: "a".to_string(),
                        ty: CType::Int8,
                        init: None,
                    },
                    CStmt::Declaration {
                        name: "b".to_string(),
                        ty: CType::Int16,
                        init: None,
                    },
                    CStmt::Declaration {
                        name: "c".to_string(),
                        ty: CType::Int32,
                        init: None,
                    },
                    CStmt::Declaration {
                        name: "d".to_string(),
                        ty: CType::Int64,
                        init: None,
                    },
                ],
            }],
        };

        writer.write_c_file(&program).unwrap();
        let output = writer.finish();

        // Check standard C type names
        assert!(output.contains("signed char a;"));
        assert!(output.contains("short b;"));
        assert!(output.contains("int c;"));
        assert!(output.contains("long long d;"));
    }

    #[test]
    fn test_formatting_with_long_lines() {
        let mut writer = CWriter::new();
        let program = CFile {
            decls: vec![CDecl::Function {
                name: "long_params".to_string(),
                return_type: CType::Int32,
                params: vec![
                    CParam {
                        name: "very_long_parameter_name_1".to_string(),
                        ty: CType::Int32,
                    },
                    CParam {
                        name: "very_long_parameter_name_2".to_string(),
                        ty: CType::Int32,
                    },
                ],
                body: vec![],
            }],
        };

        writer.write_c_file(&program).unwrap();
        let output = writer.finish();
        let lines: Vec<&str> = output.lines().collect();

        // Check that parameters are on separate lines
        assert!(lines
            .iter()
            .any(|line| line.contains("very_long_parameter_name_1")));
        assert!(lines
            .iter()
            .any(|line| line.contains("very_long_parameter_name_2")));

        // Check that parameters appear on different lines
        let param1_line = lines
            .iter()
            .position(|line| line.contains("very_long_parameter_name_1"))
            .unwrap();
        let param2_line = lines
            .iter()
            .position(|line| line.contains("very_long_parameter_name_2"))
            .unwrap();
        assert_ne!(param1_line, param2_line);

        // Check proper indentation
        assert!(lines[param1_line].starts_with("    "));
        assert!(lines[param2_line].starts_with("    "));
    }

    #[test]
    fn test_operator_spacing() {
        let mut writer = CWriter::with_options(FormattingOptions {
            space_around_operators: false,
            ..Default::default()
        });

        let expr = CExpr::Binary {
            op: CBinaryOp::Add,
            lhs: Box::new(CExpr::LiteralInt(1)),
            rhs: Box::new(CExpr::LiteralInt(2)),
        };

        writer.write_expr(&expr).unwrap();
        let output = writer.finish();
        assert_eq!(output, "1+2"); // No spaces around operator

        let mut writer = CWriter::with_options(FormattingOptions {
            space_around_operators: true,
            ..Default::default()
        });

        writer.write_expr(&expr).unwrap();
        let output = writer.finish();
        assert_eq!(output, "1 + 2"); // Spaces around operator
    }
}

// Add source mapping support
#[derive(Debug, Clone)]
pub struct SourceMapEntry {
    pub generated_line: usize,
    pub generated_column: usize,
    pub original_line: usize,
    pub original_column: usize,
    pub source_file: String,
}

#[derive(Default)]
pub struct SourceMap {
    entries: Vec<SourceMapEntry>,
}

impl SourceMap {
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    pub fn add_entry(&mut self, entry: SourceMapEntry) {
        self.entries.push(entry);
    }

    pub fn get_original_location(
        &self,
        generated_line: usize,
        generated_column: usize,
    ) -> Option<&SourceMapEntry> {
        self.entries.iter().find(|entry| {
            entry.generated_line == generated_line && entry.generated_column == generated_column
        })
    }
}
