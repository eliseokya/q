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
pub mod hotreload;
pub mod discovery;
pub mod fallback;
pub mod heuristics;

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

// Phase 3 exports
pub use hotreload::{FilesystemWatcher, EventHandler, WatchEvent, HotReloadManager};
pub use discovery::{PatternComposer, CompositePattern, StructureAnalyzer, PatternStructure};

// Phase 4 exports - NEW!
pub use fallback::{
    AnalysisResult as EnhancedAnalysisResult, ResultBuilder, 
    RejectionReason, SuggestedFix, FixType, RiskLevel, RiskAssessment,
    SafetyAnalysis, RecommendedAction, PartialAnalysis, SafetyReport,
};
pub use heuristics::{
    StructuralAnalyzer, StructuralAnalysis, SafetyHeuristics, ExtendedSafetyChecks,
};

// Re-export dependencies for use in main.rs
pub use serde_json;
