//! Analyzer library for pattern matching against mathematical theorems

pub mod common;
pub mod engine;

// Re-export main types for external use
pub use common::{
    Bundle, AnalysisResult, ProvenPattern, PatternMatch, SafetyProperty,
    ValidationError, RiskProfile, VariableBinding,
};

pub use engine::{AnalyzerEngine, AnalyzerConfig};

// Re-export dependencies for use in main.rs
pub use serde_json;
