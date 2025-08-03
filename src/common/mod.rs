//! Common types and utilities for the analyzer module
//! 
//! This module contains the core data structures used throughout the analyzer,
//! including pattern definitions, analysis results, and the tiered fallback system.

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