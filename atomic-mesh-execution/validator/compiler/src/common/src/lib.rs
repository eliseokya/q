//! Common types and utilities shared across compiler components

pub mod types;
pub mod errors;
pub mod rational;
pub mod pipeline_standards;

// Re-export commonly used types
pub use types::{
    Rational, Token, Protocol, Chain, Action, Expr, Constraint, Bundle,
    Metadata, PipelineData, TypedAction, Invariant
};

// Re-export error types and utilities
pub use errors::{
    CompilerError, read_stdin, write_stdout,
    parse_errors, transform_errors, build_errors, assemble_errors
};