//! Enhanced Analysis Result system with tiered fallback support
//! 
//! This module implements the comprehensive result types that support
//! graceful degradation from full mathematical proofs to heuristic analysis.

use crate::common::pattern_types::{ProvenPattern, SafetyProperty};
use std::collections::HashMap;
use thiserror::Error;

/// Detailed error types for rejected bundles
#[derive(Debug, Error, Clone)]
pub enum RejectionReason {
    #[error("Pattern structure is malformed: {details}")]
    MalformedStructure { details: String },
    
    #[error("Safety violation detected: {property:?} - {details}")]
    SafetyViolation { 
        property: SafetyProperty,
        details: String 
    },
    
    #[error("Constraint violation: {constraint} - {details}")]
    ConstraintViolation {
        constraint: String,
        details: String
    },
    
    #[error("Insufficient liquidity: need {required}, available {available}")]
    InsufficientLiquidity {
        required: String,
        available: String
    },
    
    #[error("Unsupported protocol: {protocol}")]
    UnsupportedProtocol { protocol: String },
    
    #[error("Cross-chain timing conflict: {details}")]
    TimingConflict { details: String },
    
    #[error("Unknown pattern with high risk: {risk_score}")]
    HighRiskPattern { risk_score: f64 },
}

/// Suggested fixes for rejected bundles
#[derive(Debug, Clone)]
pub struct SuggestedFix {
    pub fix_type: FixType,
    pub description: String,
    pub estimated_impact: String,
}

#[derive(Debug, Clone)]
pub enum FixType {
    AdjustAmount,
    ChangeProtocol,
    AddBridge,
    SplitBundle,
    WaitForLiquidity,
    SimplifyStructure,
}

/// Enhanced tiered analysis result with comprehensive fallback
#[derive(Debug)]
pub enum AnalysisResult {
    /// Perfect match with mathematical proof
    FullMatch {
        pattern: ProvenPattern,
        theorem_reference: String,
        confidence: f64, // Always 1.0 for full matches
        safety_guarantees: Vec<SafetyProperty>,
        gas_optimization_available: bool,
        execution_plan: String,
        proof_certificate: String,
    },
    
    /// Structural match with heuristic validation
    PartialMatch {
        pattern_similarity: f64, // 0.7-0.95
        matched_structure: String,
        validated_properties: Vec<SafetyProperty>,
        unverified_properties: Vec<SafetyProperty>,
        confidence: f64, // 0.5-0.95
        risk_factors: Vec<String>,
        execution_plan: String,
        warnings: Vec<String>,
    },
    
    /// Best-effort analysis for unknown patterns
    Heuristic {
        pattern_type: String,
        confidence: f64, // 0.1-0.5
        risk_assessment: RiskAssessment,
        safety_analysis: SafetyAnalysis,
        recommended_action: RecommendedAction,
        manual_review_required: bool,
        execution_plan: Option<String>,
    },
    
    /// Detailed rejection with actionable feedback
    Reject {
        reasons: Vec<RejectionReason>,
        suggested_fixes: Vec<SuggestedFix>,
        partial_analysis: Option<PartialAnalysis>,
        safety_report: SafetyReport,
    },
}

/// Risk assessment for heuristic analysis
#[derive(Debug)]
pub struct RiskAssessment {
    pub overall_risk: RiskLevel,
    pub risk_factors: HashMap<String, f64>,
    pub mitigation_strategies: Vec<String>,
    pub confidence_in_assessment: f64,
}

#[derive(Debug, Clone, PartialEq)]
pub enum RiskLevel {
    Low,      // Safe to execute with monitoring
    Medium,   // Execute with additional safeguards
    High,     // Manual review recommended
    Critical, // Do not execute without manual approval
}

/// Safety analysis for patterns without formal proofs
#[derive(Debug)]
pub struct SafetyAnalysis {
    pub balance_preserved: Option<bool>,
    pub atomicity_likely: Option<bool>,
    pub revert_safe: Option<bool>,
    pub value_extraction_risk: Option<f64>,
    pub confidence_per_property: HashMap<SafetyProperty, f64>,
}

/// Recommended action based on analysis
#[derive(Debug)]
pub enum RecommendedAction {
    ExecuteWithMonitoring,
    ExecuteWithSafeguards { safeguards: Vec<String> },
    RequireManualApproval,
    RejectAndSuggestAlternative,
}

/// Partial analysis data for rejected bundles
#[derive(Debug)]
pub struct PartialAnalysis {
    pub valid_segments: Vec<String>,
    pub problematic_segments: Vec<String>,
    pub salvageable: bool,
    pub modification_suggestions: Vec<String>,
}

/// Comprehensive safety report
#[derive(Debug)]
pub struct SafetyReport {
    pub atomicity_analysis: String,
    pub balance_analysis: String,
    pub protocol_safety: HashMap<String, bool>,
    pub cross_chain_risks: Vec<String>,
    pub overall_safety_score: f64,
}

impl AnalysisResult {
    /// Get confidence score regardless of result type
    pub fn confidence(&self) -> f64 {
        match self {
            AnalysisResult::FullMatch { confidence, .. } => *confidence,
            AnalysisResult::PartialMatch { confidence, .. } => *confidence,
            AnalysisResult::Heuristic { confidence, .. } => *confidence,
            AnalysisResult::Reject { .. } => 0.0,
        }
    }
    
    /// Check if result recommends execution
    pub fn is_executable(&self) -> bool {
        match self {
            AnalysisResult::FullMatch { .. } => true,
            AnalysisResult::PartialMatch { confidence, .. } => *confidence >= 0.7,
            AnalysisResult::Heuristic { recommended_action, .. } => {
                matches!(
                    recommended_action,
                    RecommendedAction::ExecuteWithMonitoring |
                    RecommendedAction::ExecuteWithSafeguards { .. }
                )
            }
            AnalysisResult::Reject { .. } => false,
        }
    }
    
    /// Get human-readable summary
    pub fn summary(&self) -> String {
        match self {
            AnalysisResult::FullMatch { pattern, confidence, .. } => {
                format!("Full match with pattern '{}' (confidence: {:.2})", 
                    pattern.pattern_id, confidence)
            }
            AnalysisResult::PartialMatch { pattern_similarity, confidence, .. } => {
                format!("Partial match with {:.0}% similarity (confidence: {:.2})", 
                    pattern_similarity * 100.0, confidence)
            }
            AnalysisResult::Heuristic { pattern_type, confidence, risk_assessment, .. } => {
                format!("Heuristic analysis of '{}' pattern (confidence: {:.2}, risk: {:?})", 
                    pattern_type, confidence, risk_assessment.overall_risk)
            }
            AnalysisResult::Reject { reasons, .. } => {
                format!("Rejected: {}", reasons.iter()
                    .map(|r| r.to_string())
                    .collect::<Vec<_>>()
                    .join(", "))
            }
        }
    }
    
    /// Get detailed report for logging/debugging
    pub fn detailed_report(&self) -> String {
        match self {
            AnalysisResult::FullMatch { 
                pattern, 
                theorem_reference, 
                safety_guarantees, 
                proof_certificate,
                .. 
            } => {
                format!(
                    "FULL MATCH\n\
                    Pattern: {}\n\
                    Theorem: {}\n\
                    Safety Guarantees: {:?}\n\
                    Proof Certificate: {}\n",
                    pattern.pattern_id, theorem_reference, safety_guarantees, proof_certificate
                )
            }
            AnalysisResult::PartialMatch { 
                matched_structure,
                validated_properties,
                unverified_properties,
                risk_factors,
                warnings,
                ..
            } => {
                format!(
                    "PARTIAL MATCH\n\
                    Structure: {}\n\
                    Validated: {:?}\n\
                    Unverified: {:?}\n\
                    Risks: {:?}\n\
                    Warnings: {:?}\n",
                    matched_structure, validated_properties, unverified_properties, 
                    risk_factors, warnings
                )
            }
            AnalysisResult::Heuristic {
                pattern_type,
                risk_assessment,
                safety_analysis,
                manual_review_required,
                ..
            } => {
                format!(
                    "HEURISTIC ANALYSIS\n\
                    Pattern Type: {}\n\
                    Risk Level: {:?}\n\
                    Risk Factors: {:?}\n\
                    Balance Preserved: {:?}\n\
                    Atomicity Likely: {:?}\n\
                    Manual Review Required: {}\n",
                    pattern_type, risk_assessment.overall_risk, risk_assessment.risk_factors,
                    safety_analysis.balance_preserved, safety_analysis.atomicity_likely,
                    manual_review_required
                )
            }
            AnalysisResult::Reject {
                reasons,
                suggested_fixes,
                safety_report,
                ..
            } => {
                format!(
                    "REJECTION\n\
                    Reasons: {:?}\n\
                    Suggested Fixes: {:?}\n\
                    Safety Score: {:.2}\n",
                    reasons, suggested_fixes, safety_report.overall_safety_score
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_confidence_extraction() {
        let full_match = AnalysisResult::FullMatch {
            pattern: ProvenPattern {
                pattern_id: "test".to_string(),
                pattern_template: crate::common::pattern_types::PatternTemplate::FlashLoan,
                theorem_reference: "test".to_string(),
                theorem_file: std::path::PathBuf::from("test.lean"),
                theorem_line: 1,
                safety_properties: vec![],
                preconditions: vec![],
                structure_regex: ".*".to_string(),
                confidence_threshold: 0.7,
                gas_optimization_potential: false,
            },
            theorem_reference: "test".to_string(),
            confidence: 1.0,
            safety_guarantees: vec![],
            gas_optimization_available: false,
            execution_plan: "test".to_string(),
            proof_certificate: "test".to_string(),
        };
        
        assert_eq!(full_match.confidence(), 1.0);
        assert!(full_match.is_executable());
    }
    
    #[test]
    fn test_risk_levels() {
        assert_ne!(RiskLevel::Low, RiskLevel::Critical);
        assert_eq!(RiskLevel::High, RiskLevel::High);
    }
}