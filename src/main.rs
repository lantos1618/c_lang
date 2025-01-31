use c_ast::{CBinaryOp, CDecl, CExpr, CFile, CParam, CStmt, CType};

fn main() {
    // Create a simple C program that calculates factorial
    let factorial_program = CFile {
        decls: vec![
            // int factorial(int n)
            CDecl::Function {
                name: "factorial".to_string(),
                return_type: CType::Int,
                params: vec![CParam {
                    name: "n".to_string(),
                    ty: CType::Int,
                }],
                body: vec![
                    // if (n <= 1) return 1;
                    CStmt::If {
                        cond: CExpr::Binary {
                            op: CBinaryOp::Le,
                            lhs: Box::new(CExpr::Variable("n".to_string())),
                            rhs: Box::new(CExpr::LiteralInt(1)),
                        },
                        then_branch: Box::new(CStmt::Return(Some(CExpr::LiteralInt(1)))),
                        else_branch: None,
                    },
                    // return n * factorial(n - 1);
                    CStmt::Return(Some(CExpr::Binary {
                        op: CBinaryOp::Mul,
                        lhs: Box::new(CExpr::Variable("n".to_string())),
                        rhs: Box::new(CExpr::Call {
                            func: Box::new(CExpr::Variable("factorial".to_string())),
                            args: vec![CExpr::Binary {
                                op: CBinaryOp::Sub,
                                lhs: Box::new(CExpr::Variable("n".to_string())),
                                rhs: Box::new(CExpr::LiteralInt(1)),
                            }],
                        }),
                    })),
                ],
            },
            // int main()
            CDecl::Function {
                name: "main".to_string(),
                return_type: CType::Int,
                params: vec![],
                body: vec![
                    // int result = factorial(5);
                    CStmt::Declaration {
                        name: "result".to_string(),
                        ty: CType::Int,
                        init: Some(CExpr::Call {
                            func: Box::new(CExpr::Variable("factorial".to_string())),
                            args: vec![CExpr::LiteralInt(5)],
                        }),
                    },
                    // return result;
                    CStmt::Return(Some(CExpr::Variable("result".to_string()))),
                ],
            },
        ],
    };

    let mut writer = c_ast::CWriter::new();
    writer.write_c_file(&factorial_program);
    println!("{}", writer.finish());
}
