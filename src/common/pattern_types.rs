//! Core pattern matching types for the analyzer module
//! 
//! These types define the fundamental structures for pattern recognition,
//! mathematical theorem integration, and confidence scoring.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use uuid::Uuid;

/// A proven pattern backed by a mathematical theorem from the maths/ folder
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProvenPattern {
    /// Unique identifier for this pattern
    pub id: String,
    
    /// Human-readable name for the pattern
    pub name: String,
    
    /// Reference to the Lean theorem that proves this pattern's correctness
    pub lean_theorem: String,
    
    /// Structural template for fast pattern matching
    pub structural_template: PatternTemplate,
    
    /// Mathematical safety properties guaranteed by this pattern
    pub safety_properties: Vec<SafetyProperty>,
    
    /// Computational complexity class for performance estimation
    pub performance_class: ComplexityClass,
    
    /// Confidence level when this pattern matches (always 1.0 for proven patterns)
    pub confidence: f64,
}

/// Template for structural pattern matching against DSL expressions
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PatternTemplate {
    /// Flash loan pattern: borrow → operations → repay
    FlashLoan {
        borrow_action: ActionPattern,
        repay_action: ActionPattern,
        operations: Vec<PatternTemplate>,
    },
    
    /// Cross-chain arbitrage: onChain(A) → bridge(A,B) → onChain(B)
    CrossChainArbitrage {
        source_chain: ChainPattern,
        target_chain: ChainPattern,
        operations: Vec<PatternTemplate>,
    },
    
    /// Sequential composition: pattern1 then pattern2
    Sequential {
        first: Box<PatternTemplate>,
        second: Box<PatternTemplate>,
    },
    
    /// Parallel composition: multiple patterns executing concurrently
    Parallel {
        patterns: Vec<PatternTemplate>,
    },
    
    /// Single action pattern
    Action {
        action_pattern: ActionPattern,
    },
    
    /// Chain-specific execution
    OnChain {
        chain: ChainPattern,
        pattern: Box<PatternTemplate>,
    },
    
    /// Wildcard pattern (matches anything)
    Wildcard,
}

/// Pattern for matching specific actions
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ActionPattern {
    /// Borrow action with optional constraints
    Borrow {
        token: TokenPattern,
        amount: AmountPattern,
        protocol: ProtocolPattern,
    },
    
    /// Repay action with optional constraints
    Repay {
        token: TokenPattern,
        amount: AmountPattern,
        protocol: ProtocolPattern,
    },
    
    /// Swap action with optional constraints
    Swap {
        token_in: TokenPattern,
        token_out: TokenPattern,
        amount_in: AmountPattern,
        protocol: ProtocolPattern,
    },
    
    /// Bridge action with optional constraints
    Bridge {
        to_chain: ChainPattern,
        token: TokenPattern,
        amount: AmountPattern,
    },
    
    /// Deposit action
    Deposit {
        token: TokenPattern,
        amount: AmountPattern,
        protocol: ProtocolPattern,
    },
    
    /// Withdraw action
    Withdraw {
        token: TokenPattern,
        amount: AmountPattern,
        protocol: ProtocolPattern,
    },
    
    /// Wildcard action (matches any action)
    Any,
}

/// Pattern for matching tokens
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TokenPattern {
    /// Specific token
    Specific(super::Token),
    /// Variable that must be consistent across the pattern
    Variable(String),
    /// Any token
    Any,
    /// Same as another variable (for matching consistency)
    SameAs(String),
}

/// Pattern for matching amounts
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AmountPattern {
    /// Exact amount
    Exact(super::Rational),
    /// Variable amount
    Variable(String),
    /// Any amount
    Any,
    /// Same as another variable
    SameAs(String),
    /// Amount range
    Range { min: Option<super::Rational>, max: Option<super::Rational> },
}

/// Pattern for matching protocols
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ProtocolPattern {
    /// Specific protocol
    Specific(super::Protocol),
    /// Variable protocol
    Variable(String),
    /// Any protocol
    Any,
    /// Same as another variable
    SameAs(String),
}

/// Pattern for matching chains
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ChainPattern {
    /// Specific chain
    Specific(super::Chain),
    /// Variable chain
    Variable(String),
    /// Any chain
    Any,
    /// Same as another variable
    SameAs(String),
}

/// Mathematical safety properties that patterns can guarantee
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum SafetyProperty {
    /// Bundle is atomic (all-or-nothing execution)
    Atomic,
    /// Balance is preserved (no tokens created/destroyed)
    BalancePreserving,
    /// Gas consumption is bounded
    GasBounded,
    /// Execution respects deadlines
    DeadlineRespecting,
    /// Cross-chain safety properties are maintained
    CrossChainSafe,
    /// Protocol invariants are preserved
    InvariantPreserving,
}

/// Computational complexity classification for performance estimation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ComplexityClass {
    /// Constant time O(1)
    Constant,
    /// Linear time O(n)
    Linear,
    /// Quadratic time O(n²)
    Quadratic,
    /// Exponential time O(2^n) - should be avoided
    Exponential,
}

/// Result of attempting to match a pattern against a bundle
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PatternMatch {
    /// The pattern that was matched
    pub pattern: ProvenPattern,
    
    /// Confidence score (0.0 to 1.0)
    pub confidence: f64,
    
    /// Variable bindings from the pattern match
    pub variable_bindings: HashMap<String, VariableBinding>,
    
    /// Safety properties verified by this match
    pub verified_properties: Vec<SafetyProperty>,
    
    /// Unique ID for this match result
    pub match_id: Uuid,
}

/// Value bound to a pattern variable during matching
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum VariableBinding {
    Token(super::Token),
    Amount(super::Rational),
    Protocol(super::Protocol),
    Chain(super::Chain),
}

/// Candidate pattern during the matching process
#[derive(Debug, Clone)]
pub struct PatternCandidate {
    /// Pattern being considered
    pub pattern: ProvenPattern,
    
    /// Preliminary confidence score
    pub preliminary_confidence: f64,
    
    /// Partial variable bindings so far
    pub partial_bindings: HashMap<String, VariableBinding>,
    
    /// Which safety properties might be verified
    pub potential_properties: Vec<SafetyProperty>,
}

impl ProvenPattern {
    /// Create a new proven pattern
    pub fn new(
        id: String,
        name: String,
        lean_theorem: String,
        structural_template: PatternTemplate,
        safety_properties: Vec<SafetyProperty>,
        performance_class: ComplexityClass,
    ) -> Self {
        Self {
            id,
            name,
            lean_theorem,
            structural_template,
            safety_properties,
            performance_class,
            confidence: 1.0, // Always 1.0 for proven patterns
        }
    }
    
    /// Check if this pattern guarantees a specific safety property
    pub fn guarantees_property(&self, property: &SafetyProperty) -> bool {
        self.safety_properties.contains(property)
    }
    
    /// Get estimated execution time based on complexity class
    pub fn estimated_execution_time(&self) -> std::time::Duration {
        match self.performance_class {
            ComplexityClass::Constant => std::time::Duration::from_micros(10),
            ComplexityClass::Linear => std::time::Duration::from_micros(50),
            ComplexityClass::Quadratic => std::time::Duration::from_micros(200),
            ComplexityClass::Exponential => std::time::Duration::from_millis(1), // Should be avoided
        }
    }
}

impl PatternMatch {
    /// Create a new pattern match result
    pub fn new(
        pattern: ProvenPattern,
        confidence: f64,
        variable_bindings: HashMap<String, VariableBinding>,
        verified_properties: Vec<SafetyProperty>,
    ) -> Self {
        Self {
            pattern,
            confidence,
            variable_bindings,
            verified_properties,
            match_id: Uuid::new_v4(),
        }
    }
    
    /// Check if this match guarantees a specific safety property
    pub fn guarantees_property(&self, property: &SafetyProperty) -> bool {
        self.verified_properties.contains(property)
    }
    
    /// Get the theorem reference for this match
    pub fn theorem_reference(&self) -> &str {
        &self.pattern.lean_theorem
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_proven_pattern_creation() {
        let pattern = ProvenPattern::new(
            "flash_loan_v1".to_string(),
            "Basic Flash Loan".to_string(),
            "maths.Stack.Bundles.flash_loan_atomic".to_string(),
            PatternTemplate::FlashLoan {
                borrow_action: ActionPattern::Borrow {
                    token: TokenPattern::Variable("X".to_string()),
                    amount: AmountPattern::Variable("A".to_string()),
                    protocol: ProtocolPattern::Any,
                },
                repay_action: ActionPattern::Repay {
                    token: TokenPattern::SameAs("X".to_string()),
                    amount: AmountPattern::SameAs("A".to_string()),
                    protocol: ProtocolPattern::Any,
                },
                operations: vec![PatternTemplate::Wildcard],
            },
            vec![SafetyProperty::Atomic, SafetyProperty::BalancePreserving],
            ComplexityClass::Linear,
        );
        
        assert_eq!(pattern.confidence, 1.0);
        assert!(pattern.guarantees_property(&SafetyProperty::Atomic));
        assert!(pattern.guarantees_property(&SafetyProperty::BalancePreserving));
        assert!(!pattern.guarantees_property(&SafetyProperty::GasBounded));
    }

    #[test]
    fn test_pattern_match_creation() {
        let pattern = ProvenPattern::new(
            "test_pattern".to_string(),
            "Test Pattern".to_string(),
            "test.theorem".to_string(),
            PatternTemplate::Wildcard,
            vec![SafetyProperty::Atomic],
            ComplexityClass::Constant,
        );
        
        let mut bindings = HashMap::new();
        bindings.insert(
            "X".to_string(),
            VariableBinding::Token(super::Token::WETH),
        );
        
        let pattern_match = PatternMatch::new(
            pattern,
            0.95,
            bindings,
            vec![SafetyProperty::Atomic],
        );
        
        assert_eq!(pattern_match.confidence, 0.95);
        assert!(pattern_match.guarantees_property(&SafetyProperty::Atomic));
        assert_eq!(pattern_match.theorem_reference(), "test.theorem");
    }
}