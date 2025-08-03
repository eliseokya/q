//! Error handling utilities for compiler components

use serde::{Deserialize, Serialize};
use std::error::Error;

/// Standard error structure for all compiler components
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompilerError {
    pub error: bool,
    pub component: String,
    pub code: String,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub context: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub suggestion: Option<String>,
}

impl CompilerError {
    pub fn new(component: &str, code: &str, message: String) -> Self {
        Self {
            error: true,
            component: component.to_string(),
            code: code.to_string(),
            message,
            context: None,
            suggestion: None,
        }
    }

    pub fn with_context(mut self, context: serde_json::Value) -> Self {
        self.context = Some(context);
        self
    }

    pub fn with_suggestion(mut self, suggestion: String) -> Self {
        self.suggestion = Some(suggestion);
        self
    }

    /// Exit the process with error code
    pub fn exit(self, code: i32) -> ! {
        eprintln!("{}", serde_json::to_string(&self).unwrap());
        std::process::exit(code);
    }
}

impl std::fmt::Display for CompilerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}] {}: {}", self.component, self.code, self.message)
    }
}

impl Error for CompilerError {}

/// Error codes for parse-and-validate
pub mod parse_errors {
    pub const MALFORMED_JSON: &str = "MALFORMED_JSON";
    pub const MISSING_FIELD: &str = "MISSING_FIELD";
    pub const INVALID_TYPE: &str = "INVALID_TYPE";
    pub const EMPTY_ACTIONS: &str = "EMPTY_ACTIONS";
}

/// Error codes for transform-actions
pub mod transform_errors {
    pub const UNKNOWN_TOKEN: &str = "UNKNOWN_TOKEN";
    pub const UNKNOWN_PROTOCOL: &str = "UNKNOWN_PROTOCOL";
    pub const UNKNOWN_CHAIN: &str = "UNKNOWN_CHAIN";
    pub const INVALID_AMOUNT: &str = "INVALID_AMOUNT";
    pub const NEGATIVE_AMOUNT: &str = "NEGATIVE_AMOUNT";
    pub const CHAIN_INFERENCE_FAILED: &str = "CHAIN_INFERENCE_FAILED";
    pub const MISSING_ACTION_FIELD: &str = "MISSING_ACTION_FIELD";
    pub const MISSING_FIELD: &str = "MISSING_FIELD";
    pub const MISSING_ACTIONS: &str = "MISSING_ACTIONS";
    pub const INVALID_ACTION: &str = "INVALID_ACTION";
    pub const CHAIN_MISMATCH: &str = "CHAIN_MISMATCH";
    pub const INVALID_ACTION_SEQUENCE: &str = "INVALID_ACTION_SEQUENCE";
}

/// Error codes for build-expression
pub mod build_errors {
    pub const INVALID_ACTION_SEQUENCE: &str = "INVALID_ACTION_SEQUENCE";
    pub const CHAIN_MISMATCH: &str = "CHAIN_MISMATCH";
    pub const EMPTY_EXPRESSION: &str = "EMPTY_EXPRESSION";
    pub const PARALLEL_CONFLICT: &str = "PARALLEL_CONFLICT";
    pub const EMPTY_ACTIONS: &str = "EMPTY_ACTIONS";
    pub const MISSING_TYPED_ACTIONS: &str = "MISSING_TYPED_ACTIONS";
}

/// Error codes for assemble-bundle
pub mod assemble_errors {
    pub const ASSEMBLY_FAILED: &str = "ASSEMBLY_FAILED";
    pub const INVALID_CONSTRAINT: &str = "INVALID_CONSTRAINT";
    pub const MISSING_START_CHAIN: &str = "MISSING_START_CHAIN";
    pub const MISSING_EXPRESSION: &str = "MISSING_EXPRESSION";
    pub const INVALID_CHAIN: &str = "INVALID_CHAIN";
    pub const INVALID_CONSTRAINTS: &str = "INVALID_CONSTRAINTS";
    pub const INVALID_CONSTRAINT_VALUE: &str = "INVALID_CONSTRAINT_VALUE";
}

/// Helper function to read from stdin
pub fn read_stdin() -> Result<String, Box<dyn Error>> {
    use std::io::{self, Read};
    let mut buffer = String::new();
    io::stdin().read_to_string(&mut buffer)?;
    Ok(buffer)
}

/// Helper function to write to stdout
pub fn write_stdout<T: Serialize>(data: &T) -> Result<(), Box<dyn Error>> {
    println!("{}", serde_json::to_string(data)?);
    Ok(())
}