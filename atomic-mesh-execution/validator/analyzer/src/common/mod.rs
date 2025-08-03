//! Common types and utilities for the analyzer module

pub mod pattern_types;
pub mod analysis_result;

// Re-export commonly used types
pub use pattern_types::{
    ProvenPattern, PatternTemplate, PatternMatch, PatternCandidate,
    ActionPattern, TokenPattern, AmountPattern, ProtocolPattern, ChainPattern,
    SafetyProperty, ComplexityClass, VariableBinding,
};

pub use analysis_result::{
    AnalysisResult, ValidationRecommendation, RiskProfile, RiskFactor,
    RiskRecommendation, ValidationError, BundleAnalysis, ComplexityEstimate,
};

// Re-export types from the compiler's common module
pub use common::{Bundle, Expr, Action, Token, Protocol, Chain, Constraint, Rational};
