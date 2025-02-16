//! C Language Compiler
//!
//! This binary provides a command-line interface to the c_lang compiler.
//! It demonstrates the compilation process from high-level AST to C code,
//! as well as direct C AST manipulation.

use c_lang::{
    code_gen_error, lowering_error, AstLowering, BinaryOp, CBinaryOp, CDecl, CExpr, CFile, CParam,
    CStmt, CType, CWriter, CompilerError, Decl, Expr, IntSize, Literal, Module, Parameter, Result,
    SourceLocation, Stmt, Type,
};
use log::{debug, error, info};
use std::{error::Error, process};

/// Creates a high-level AST for the factorial function.
///
/// This example demonstrates how to create a high-level AST that will be
/// lowered to C code. The factorial function is implemented recursively.
fn create_factorial_program() -> Module {
    info!("Creating high-level AST for factorial program");
    Module {
        decls: vec![
            // Factorial function declaration
            Decl::Function {
                name: "factorial".to_string(),
                params: vec![Parameter {
                    name: "n".to_string(),
                    ty: Type::Int(IntSize::I32),
                }],
                return_type: Type::Int(IntSize::I32),
                body: Some(vec![
                    // if (n <= 1) return 1;
                    Stmt::Block(vec![Stmt::While {
                        cond: Expr::Binary {
                            op: BinaryOp::Le,
                            left: Box::new(Expr::Variable("n".to_string())),
                            right: Box::new(Expr::Literal(Literal::Int(1))),
                        },
                        body: vec![
                            Stmt::Return(Some(Expr::Literal(Literal::Int(1)))),
                            Stmt::Break,
                        ],
                    }]),
                    // return n * factorial(n - 1);
                    Stmt::Return(Some(Expr::Binary {
                        op: BinaryOp::Mul,
                        left: Box::new(Expr::Variable("n".to_string())),
                        right: Box::new(Expr::Call {
                            func: Box::new(Expr::Variable("factorial".to_string())),
                            args: vec![Expr::Binary {
                                op: BinaryOp::Sub,
                                left: Box::new(Expr::Variable("n".to_string())),
                                right: Box::new(Expr::Literal(Literal::Int(1))),
                            }],
                        }),
                    })),
                ]),
            },
            // Main function declaration
            Decl::Function {
                name: "main".to_string(),
                params: vec![],
                return_type: Type::Int(IntSize::I32),
                body: Some(vec![
                    // int result = factorial(5);
                    Stmt::Let {
                        name: "result".to_string(),
                        ty: Some(Type::Int(IntSize::I32)),
                        value: Expr::Call {
                            func: Box::new(Expr::Variable("factorial".to_string())),
                            args: vec![Expr::Literal(Literal::Int(5))],
                        },
                    },
                    // return result;
                    Stmt::Return(Some(Expr::Variable("result".to_string()))),
                ]),
            },
        ],
    }
}

/// Creates a C AST for the factorial function.
///
/// This example demonstrates direct manipulation of the C AST,
/// bypassing the high-level AST and lowering process.
fn create_c_factorial_program() -> CFile {
    info!("Creating C AST for factorial program");
    CFile {
        decls: vec![
            // int factorial(int n)
            CDecl::Function {
                name: "factorial".to_string(),
                return_type: CType::Int32,
                params: vec![CParam {
                    name: "n".to_string(),
                    ty: CType::Int32,
                }],
                body: vec![
                    // if (n <= 1) return 1;
                    CStmt::If {
                        cond: CExpr::Binary {
                            op: CBinaryOp::Le,
                            lhs: Box::new(CExpr::Variable("n".to_string())),
                            rhs: Box::new(CExpr::LiteralInt(1)),
                        },
                        then_branch: Box::new(CStmt::Block(vec![CStmt::Return(Some(
                            CExpr::LiteralInt(1),
                        ))])),
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
                return_type: CType::Int32,
                params: vec![],
                body: vec![
                    // int result = factorial(5);
                    CStmt::Declaration {
                        name: "result".to_string(),
                        ty: CType::Int32,
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
    }
}

/// Compiles a high-level AST module to C code.
///
/// This function demonstrates the full compilation pipeline:
/// 1. AST lowering (high-level AST → C AST)
/// 2. Code generation (C AST → C code)
fn compile(source: &Module) -> Result<String> {
    debug!("Starting compilation");

    // Create AST lowering instance
    let mut lowering = AstLowering::new();
    debug!("Created AST lowering instance");

    // Lower the high-level AST to C AST
    let c_ast = lowering.lower_module(source).map_err(|e| {
        error!("AST lowering failed: {}", e);
        lowering_error!(SourceLocation::unknown(), "Failed to lower AST: {}", e)
    })?;
    debug!("Successfully lowered AST to C AST");

    // Create C writer with default options
    let mut writer = CWriter::new();
    debug!("Created C writer");

    // Generate C code
    writer.write_c_file(&c_ast).map_err(|e| {
        error!("Code generation failed: {}", e);
        code_gen_error!("Failed to generate C code: {}", e)
    })?;
    debug!("Successfully generated C code");

    let result = writer.finish();
    info!("Compilation completed successfully");
    Ok(result)
}

fn main() {
    // Initialize logging with reasonable defaults
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info"))
        .format_timestamp(None)
        .format_target(false)
        .init();

    info!("C Language Compiler v{}", c_lang::VERSION);

    // Example 1: Direct C AST to code generation
    info!("Example 1: Direct C AST to code generation");
    println!("------------------------------------------");
    let c_program = create_c_factorial_program();
    let mut writer = CWriter::new();
    if let Err(e) = writer.write_c_file(&c_program) {
        error!("Error generating C code: {}", e);
        if let Some(source) = e.source() {
            error!("Caused by: {}", source);
        }
        process::exit(1);
    }
    println!("{}", writer.finish());

    // Example 2: High-level AST to C code compilation
    info!("\nExample 2: High-level AST to C code compilation");
    println!("----------------------------------------------");
    let high_level_program = create_factorial_program();
    match compile(&high_level_program) {
        Ok(code) => println!("{}", code),
        Err(e) => {
            error!("Compilation error: {}", e);
            if let Some(source) = e.source() {
                error!("Caused by: {}", source);
            }
            process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_factorial_compilation() {
        let program = create_factorial_program();
        let result = compile(&program);
        assert!(result.is_ok(), "Compilation failed: {:?}", result.err());

        let generated_code = result.unwrap();
        println!("Generated code:\n{}", generated_code);
        assert!(generated_code.contains("if (n <= 1)"));

        // Verify specific code patterns
        assert!(generated_code.contains("return 1;"));
        assert!(generated_code.contains("return n * factorial(n - 1);"));
    }

    #[test]
    fn test_direct_c_generation() {
        let program = create_c_factorial_program();
        let mut writer = CWriter::new();
        assert!(writer.write_c_file(&program).is_ok());

        let generated_code = writer.finish();
        assert!(generated_code.contains("factorial"));
        assert!(generated_code.contains("main"));

        // Verify the generated code structure
        let expected_fragments = [
            "int factorial(int n)",
            "if (n <= 1)",
            "return 1;",
            "return n * factorial(n - 1);",
            "int main()",
            "int result = factorial(5);",
            "return result;",
        ];

        for fragment in expected_fragments {
            assert!(
                generated_code.contains(fragment),
                "Missing expected code fragment: '{}'\nGenerated code:\n{}",
                fragment,
                generated_code
            );
        }
    }
}
