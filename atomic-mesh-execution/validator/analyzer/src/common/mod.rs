//! Common types used throughout the analyzer module
//!
//! This module combines types from the external common crate with
//! analyzer-specific pattern matching types.

pub mod pattern_types;
pub mod analysis_result;

// Re-export types from the external common crate
pub use common::{Bundle, Expr, Action, Token, Protocol, Chain, Constraint, Rational};

// Re-export analyzer-specific types
pub use pattern_types::{
    ProvenPattern, PatternTemplate, SafetyProperty, PatternCandidate,
    VariableBinding,
};

pub use analysis_result::{
    AnalysisResult, ValidationRecommendation, RiskProfile, RiskFactor,
    RiskRecommendation, ValidationError, BundleAnalysis, ComplexityEstimate,
};
