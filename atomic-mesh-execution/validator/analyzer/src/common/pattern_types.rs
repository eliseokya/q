//! Core pattern matching types for the analyzer module

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;

/// A mathematically proven pattern from the Lean 4 formalization
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProvenPattern {
    /// Unique identifier for the pattern
    pub pattern_id: String,
    
    /// Pattern template type
    pub pattern_template: PatternTemplate,
    
    /// Reference to the Lean theorem
    pub theorem_reference: String,
    
    /// File containing the theorem
    pub theorem_file: PathBuf,
    
    /// Line number in the theorem file
    pub theorem_line: usize,
    
    /// Safety properties guaranteed by this pattern
    pub safety_properties: Vec<SafetyProperty>,
    
    /// Preconditions that must be satisfied
    pub preconditions: Vec<String>,
    
    /// Regular expression for structural matching
    pub structure_regex: String,
    
    /// Minimum confidence threshold for this pattern
    pub confidence_threshold: f64,
    
    /// Whether this pattern enables gas optimization
    pub gas_optimization_potential: bool,
}

/// Template types for patterns
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum PatternTemplate {
    FlashLoan,
    CrossChainArbitrage,
    TriangularArbitrage,
    LiquidityMigration,
    ProtocolSpecific,
    GeneralAtomic,
    GasOptimization,
    BridgeOperation,
}

/// Safety properties that patterns can guarantee
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum SafetyProperty {
    Atomicity,
    BalancePreservation,
    NoReentrancy,
    CrossChainConsistency,
    BridgeSafety,
    ProtocolInvariant,
    StateConsistency,
    SemanticEquivalence,
    GasReduction,
    TimelockSafety,
    AllOrNothing,
}

/// A candidate pattern match during analysis
#[derive(Debug, Clone)]
pub struct PatternCandidate {
    /// The matched pattern
    pub pattern: ProvenPattern,
    
    /// Confidence score for this match
    pub confidence_score: f64,
    
    /// Whether structural matching succeeded
    pub structural_match: bool,
    
    /// Whether semantic validation succeeded
    pub semantic_match: bool,
    
    /// Details about the match
    pub match_details: String,
}

/// Variable bindings extracted during pattern matching
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VariableBinding {
    pub name: String,
    pub value: String,
    pub binding_type: BindingType,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum BindingType {
    Token,
    Amount,
    Protocol,
    Chain,
    Address,
    Generic,
}
