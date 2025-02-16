use std::fmt;
use thiserror::Error;

#[derive(Debug, Clone)]
pub struct SourceLocation {
    pub line: usize,
    pub column: usize,
    pub file: Option<String>,
}

impl SourceLocation {
    pub fn new(line: usize, column: usize, file: Option<String>) -> Self {
        Self { line, column, file }
    }

    pub fn unknown() -> Self {
        Self {
            line: 0,
            column: 0,
            file: None,
        }
    }
}

impl fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.file {
            Some(file) => write!(f, "{}:{}:{}", file, self.line, self.column),
            None => write!(f, "<unknown>:{}:{}", self.line, self.column),
        }
    }
}

#[derive(Error, Debug)]
pub enum CompilerError {
    #[error("Type error at {location}: {message}")]
    TypeError {
        message: String,
        location: SourceLocation,
        #[source]
        source: Option<Box<dyn std::error::Error + Send + Sync>>,
    },

    #[error("Syntax error at {location}: {message}")]
    SyntaxError {
        message: String,
        location: SourceLocation,
        #[source]
        source: Option<Box<dyn std::error::Error + Send + Sync>>,
    },

    #[error("Lowering error at {location}: {message}")]
    LoweringError {
        message: String,
        location: SourceLocation,
        #[source]
        source: Option<Box<dyn std::error::Error + Send + Sync>>,
    },

    #[error("Code generation error: {message}")]
    CodeGenError {
        message: String,
        #[source]
        source: Option<Box<dyn std::error::Error + Send + Sync>>,
    },

    #[error("IO error: {message}")]
    IoError {
        message: String,
        #[source]
        source: std::io::Error,
    },

    #[error("Internal compiler error: {message}")]
    InternalError {
        message: String,
        #[source]
        source: Option<Box<dyn std::error::Error + Send + Sync>>,
    },
}

impl CompilerError {
    pub fn type_error(message: impl Into<String>, location: SourceLocation) -> Self {
        Self::TypeError {
            message: message.into(),
            location,
            source: None,
        }
    }

    pub fn syntax_error(message: impl Into<String>, location: SourceLocation) -> Self {
        Self::SyntaxError {
            message: message.into(),
            location,
            source: None,
        }
    }

    pub fn lowering_error(message: impl Into<String>, location: SourceLocation) -> Self {
        Self::LoweringError {
            message: message.into(),
            location,
            source: None,
        }
    }

    pub fn code_gen_error(message: impl Into<String>) -> Self {
        Self::CodeGenError {
            message: message.into(),
            source: None,
        }
    }

    pub fn internal_error(message: impl Into<String>) -> Self {
        Self::InternalError {
            message: message.into(),
            source: None,
        }
    }

    pub fn io_error(message: impl Into<String>, source: std::io::Error) -> Self {
        Self::IoError {
            message: message.into(),
            source,
        }
    }

    pub fn with_source<E>(self, source: E) -> Self
    where
        E: std::error::Error + Send + Sync + 'static,
    {
        match self {
            Self::TypeError {
                message, location, ..
            } => Self::TypeError {
                message,
                location,
                source: Some(Box::new(source)),
            },
            Self::SyntaxError {
                message, location, ..
            } => Self::SyntaxError {
                message,
                location,
                source: Some(Box::new(source)),
            },
            Self::LoweringError {
                message, location, ..
            } => Self::LoweringError {
                message,
                location,
                source: Some(Box::new(source)),
            },
            Self::CodeGenError { message, .. } => Self::CodeGenError {
                message,
                source: Some(Box::new(source)),
            },
            Self::InternalError { message, .. } => Self::InternalError {
                message,
                source: Some(Box::new(source)),
            },
            Self::IoError { .. } => self, // IoError has a specific source type
        }
    }
}

impl From<std::io::Error> for CompilerError {
    fn from(error: std::io::Error) -> Self {
        CompilerError::IoError {
            message: error.to_string(),
            source: error,
        }
    }
}

pub type Result<T> = std::result::Result<T, CompilerError>;

// Convenience macros for error creation
#[macro_export]
macro_rules! type_error {
    ($loc:expr, $msg:expr) => {
        $crate::errors::CompilerError::type_error($msg, $loc)
    };
    ($loc:expr, $fmt:expr, $($arg:tt)*) => {
        $crate::errors::CompilerError::type_error(format!($fmt, $($arg)*), $loc)
    };
}

#[macro_export]
macro_rules! syntax_error {
    ($loc:expr, $msg:expr) => {
        $crate::errors::CompilerError::syntax_error($msg, $loc)
    };
    ($loc:expr, $fmt:expr, $($arg:tt)*) => {
        $crate::errors::CompilerError::syntax_error(format!($fmt, $($arg)*), $loc)
    };
}

#[macro_export]
macro_rules! lowering_error {
    ($loc:expr, $msg:expr) => {
        $crate::errors::CompilerError::lowering_error($msg, $loc)
    };
    ($loc:expr, $fmt:expr, $($arg:tt)*) => {
        $crate::errors::CompilerError::lowering_error(format!($fmt, $($arg)*), $loc)
    };
}

#[macro_export]
macro_rules! code_gen_error {
    ($msg:expr) => {
        $crate::errors::CompilerError::code_gen_error($msg)
    };
    ($fmt:expr, $($arg:tt)*) => {
        $crate::errors::CompilerError::code_gen_error(format!($fmt, $($arg)*))
    };
}

#[macro_export]
macro_rules! internal_error {
    ($msg:expr) => {
        $crate::errors::CompilerError::internal_error($msg)
    };
    ($fmt:expr, $($arg:tt)*) => {
        $crate::errors::CompilerError::internal_error(format!($fmt, $($arg)*))
    };
}

#[macro_export]
macro_rules! io_error {
    ($source:expr, $msg:expr) => {
        $crate::errors::CompilerError::io_error($msg, $source)
    };
    ($source:expr, $fmt:expr, $($arg:tt)*) => {
        $crate::errors::CompilerError::io_error(format!($fmt, $($arg)*), $source)
    };
}
