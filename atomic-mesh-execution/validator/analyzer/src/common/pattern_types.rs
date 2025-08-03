//! Core pattern matching types for the analyzer module

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use uuid::Uuid;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProvenPattern {
    pub id: String,
    pub name: String,
    pub lean_theorem: String,
    pub safety_properties: Vec<SafetyProperty>,
    pub confidence: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum PatternTemplate {
    FlashLoan,
    CrossChainArbitrage,
    Sequential,
    Parallel,
    Action,
    OnChain,
    Wildcard,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ActionPattern {
    Borrow, Repay, Swap, Bridge, Deposit, Withdraw, Any,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TokenPattern {
    Specific(common::Token),
    Variable(String),
    Any,
    SameAs(String),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AmountPattern {
    Exact(common::Rational),
    Variable(String),
    Any,
    SameAs(String),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ProtocolPattern {
    Specific(common::Protocol),
    Variable(String),
    Any,
    SameAs(String),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ChainPattern {
    Specific(common::Chain),
    Variable(String),
    Any,
    SameAs(String),
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum SafetyProperty {
    Atomic,
    BalancePreserving,
    GasBounded,
    DeadlineRespecting,
    CrossChainSafe,
    InvariantPreserving,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ComplexityClass {
    Constant,
    Linear,
    Quadratic,
    Exponential,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PatternMatch {
    pub pattern: ProvenPattern,
    pub confidence: f64,
    pub variable_bindings: HashMap<String, VariableBinding>,
    pub verified_properties: Vec<SafetyProperty>,
    pub match_id: Uuid,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum VariableBinding {
    Token(common::Token),
    Amount(common::Rational),
    Protocol(common::Protocol),
    Chain(common::Chain),
}

#[derive(Debug, Clone)]
pub struct PatternCandidate {
    pub pattern: ProvenPattern,
    pub preliminary_confidence: f64,
    pub partial_bindings: HashMap<String, VariableBinding>,
    pub potential_properties: Vec<SafetyProperty>,
}

impl PatternMatch {
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
}
