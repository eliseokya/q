//! Analyzer module for the Atomic Mesh VM Validator
//!
//! This module performs pattern matching against mathematical theorems
//! to validate arbitrage opportunities.

pub mod common;
pub mod engine;
pub mod pattern_scanner;
pub mod pattern_compiler;
pub mod matching;
pub mod validation;
pub mod semantic;
pub mod scoring;

// Re-export main types and functions
pub use common::{
    AnalysisResult, ValidationRecommendation, RiskProfile, RiskFactor,
    RiskRecommendation, ValidationError, BundleAnalysis, ComplexityEstimate,
    ProvenPattern, PatternCandidate, SafetyProperty, PatternTemplate,
    Bundle, Expr, Action, Token, Chain, Protocol, Constraint, VariableBinding,
};

pub use engine::{
    AnalyzerEngine, AnalyzerConfig, StaticPatternLibrary, DynamicPatternCache,
};

pub use pattern_scanner::{LeanParser, TheoremDatabase, Theorem};
pub use pattern_compiler::{LeanToPatternCompiler, AutomataGenerator, FiniteAutomaton};
pub use matching::{StructuralMatcher, AutomataMatchEngine, MatchResult};
pub use validation::{ConstraintChecker, ConstraintValidationResult};

// Phase 2 exports
pub use semantic::{TheoremEngine, TheoremError, ProofApplicationEngine, SemanticValidator};
pub use scoring::{ConfidenceCalculator, ConfidenceConfig, RiskAssessor};

// Re-export dependencies for use in main.rs
pub use serde_json;
