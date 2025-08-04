//! Simplified fallback system for graceful degradation
//! 
//! This module provides the tiered fallback system that enables
//! the analyzer to gracefully handle unknown patterns.

pub mod analysis_result;
pub mod result_builder;

pub use analysis_result::*;

// Simplified ResultBuilder that actually compiles
use crate::common::pattern_types::{ProvenPattern, SafetyProperty, PatternCandidate};
use std::collections::HashMap;

pub struct SimpleResultBuilder;

impl SimpleResultBuilder {
    pub fn new() -> Self {
        Self
    }
    
    pub fn build_full_match(pattern: ProvenPattern) -> analysis_result::AnalysisResult {
        analysis_result::AnalysisResult::FullMatch {
            pattern,
            theorem_reference: "test".to_string(),
            confidence: 1.0,
            safety_guarantees: vec![],
            gas_optimization_available: false,
            execution_plan: "test".to_string(),
            proof_certificate: "test".to_string(),
        }
    }
    
    pub fn build_reject() -> analysis_result::AnalysisResult {
        analysis_result::AnalysisResult::Reject {
            reasons: vec![],
            suggested_fixes: vec![],
            partial_analysis: None,
            safety_report: analysis_result::SafetyReport {
                atomicity_analysis: "test".to_string(),
                balance_analysis: "test".to_string(),
                protocol_safety: HashMap::new(),
                cross_chain_risks: vec![],
                overall_safety_score: 0.0,
            },
        }
    }
}