//! Simplified analysis result types for bundle generator

use serde::{Deserialize, Serialize};
use common::types::Bundle;

/// Pattern types that can be matched
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PatternType {
    FlashLoanArbitrage,
    CrossChainArbitrage,
    TriangularArbitrage,
    Unknown,
}

/// Pattern match information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PatternMatch {
    pub pattern_type: PatternType,
    pub confidence: f64,
}

/// Simplified analysis result for bundle generation
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "result_type")]
pub enum AnalysisResult {
    FullMatch {
        pattern: PatternMatch,
        bundle: Bundle,
        confidence: f64,
    },
    PartialMatch {
        pattern: PatternMatch,
        bundle: Bundle,
        issues: Vec<String>,
    },
    Heuristic {
        bundle: Bundle,
        confidence: f64,
    },
    Reject {
        error: String,
    },
}