pub mod ast_lowering;
pub mod c_ast;
pub mod c_writer;
pub mod errors;
pub mod high_level_ast;

// Re-export all public items from each module
pub use ast_lowering::*;
pub use c_ast::*;
pub use c_writer::*;
pub use high_level_ast::*;

// Re-export commonly used error types for convenience
pub use errors::{CompilerError, Result, SourceLocation};

// Version information
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const NAME: &str = env!("CARGO_PKG_NAME");
