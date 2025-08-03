//! Analysis result types for the tiered fallback system
//! 
//! Implements the FullMatch → PartialMatch → Heuristic → Reject architecture
//! for graceful degradation when patterns cannot be fully matched.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use uuid::Uuid;

use super::pattern_types::{PatternMatch, SafetyProperty, VariableBinding};

/// Complete result of analyzing a bundle through the tiered fallback system
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AnalysisResult {
    /// Tier 1: Perfect pattern match with mathematical proof
    FullMatch {
        /// The matched pattern with full mathematical backing
        pattern_match: PatternMatch,
        /// Reference to the Lean theorem that proves correctness
        theorem_reference: String,
        /// Confidence is always 1.0 for proven patterns
        confidence: f64,
        /// All safety properties guaranteed by the theorem
        safety_guarantees: Vec<SafetyProperty>,
        /// Unique analysis ID
        analysis_id: Uuid,
    },
    
    /// Tier 2: Structural match with heuristic validation
    PartialMatch {
        /// Best structural pattern match found
        pattern_match: PatternMatch,
        /// Confidence score (0.5 - 0.95 range)
        confidence: f64,
        /// Safety properties that could be validated
        validated_properties: Vec<SafetyProperty>,
        /// Safety properties that couldn't be guaranteed
        missing_guarantees: Vec<SafetyProperty>,
        /// Recommendation for how to proceed
        recommendation: ValidationRecommendation,
        /// Unique analysis ID
        analysis_id: Uuid,
    },
    
    /// Tier 3: Best-effort risk assessment for unknown patterns
    Heuristic {
        /// Risk assessment profile
        risk_assessment: RiskProfile,
        /// Confidence score (0.1 - 0.5 range)
        confidence: f64,
        /// Patterns that were partially detected
        detected_patterns: Vec<String>,
        /// Safety warnings identified
        safety_warnings: Vec<String>,
        /// Whether manual review is required
        manual_review_required: bool,
        /// Unique analysis ID
        analysis_id: Uuid,
    },
    
    /// Tier 4: Rejection with detailed error information
    Reject {
        /// The validation error that caused rejection
        error: ValidationError,
        /// Hash of the bundle that was rejected
        bundle_hash: String,
        /// Properties of the bundle that were analyzed
        analyzed_properties: BundleAnalysis,
        /// Suggestions for fixing the bundle
        suggested_fixes: Vec<String>,
        /// Unique analysis ID
        analysis_id: Uuid,
    },
}

/// Validation recommendations for partial matches
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ValidationRecommendation {
    /// Proceed with execution (high confidence partial match)
    ProceedWithCaution,
    /// Require additional validation before execution
    RequireAdditionalValidation,
    /// Recommend manual review by a human
    RecommendManualReview,
    /// Suggest modifications to the bundle
    SuggestModifications(Vec<String>),
    /// Reject due to insufficient confidence
    Reject(String),
}

/// Comprehensive risk assessment for unknown or partially matched patterns
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RiskProfile {
    /// Overall risk score (0.0 = no risk, 1.0 = maximum risk)
    pub overall_score: f64,
    /// Individual risk factors identified
    pub risk_factors: Vec<RiskFactor>,
    /// Confidence in the risk assessment itself
    pub confidence: f64,
    /// Overall recommendation based on risk analysis
    pub recommendation: RiskRecommendation,
}

/// Individual risk factors that can be identified
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RiskFactor {
    /// Bundle has high computational complexity
    HighComplexity(f64),
    /// Contains unknown or unrecognized action patterns
    UnknownActions(Vec<String>),
    /// Cross-chain operations that may not be safe
    CrossChainUnsafe(String),
    /// Gas consumption may exceed bounds
    GasRisk(String),
    /// Timing constraints may not be met
    TimingRisk(String),
    /// Balance preservation cannot be guaranteed
    BalanceRisk(String),
    /// Protocol invariants may be violated
    InvariantRisk(String),
}

/// Recommendations based on risk assessment
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RiskRecommendation {
    /// Low risk, proceed with execution
    LowRisk,
    /// Medium risk, proceed with additional monitoring
    MediumRisk,
    /// High risk, require manual approval
    HighRisk,
    /// Unacceptable risk, reject execution
    UnacceptableRisk,
}

/// Validation errors that can cause bundle rejection
#[derive(Debug, Clone, Serialize, Deserialize, thiserror::Error)]
pub enum ValidationError {
    /// No pattern could be matched against the bundle
    #[error("No matching pattern found for bundle structure")]
    UnknownPattern,
    
    /// Bundle violates mathematical constraints
    #[error("Bundle violates constraint: {constraint}")]
    ConstraintViolation { constraint: String },
    
    /// Analysis exceeded performance timeout
    #[error("Analysis timed out after {timeout_ms}ms")]
    PerformanceTimeout { timeout_ms: u64 },
    
    /// Bundle structure is malformed
    #[error("Malformed bundle structure: {details}")]
    MalformedBundle { details: String },
    
    /// Mathematical invariants would be violated
    #[error("Mathematical invariant violation: {invariant}")]
    InvariantViolation { invariant: String },
    
    /// Cross-chain safety requirements not met
    #[error("Cross-chain safety violation: {details}")]
    CrossChainSafetyViolation { details: String },
    
    /// Internal analyzer error
    #[error("Internal analyzer error: {details}")]
    InternalError { details: String },
}

/// Analysis of bundle properties (even for rejected bundles)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BundleAnalysis {
    /// Number of actions in the bundle
    pub action_count: usize,
    /// Chains involved in the bundle
    pub chains_involved: Vec<common::Chain>,
    /// Tokens involved in the bundle
    pub tokens_involved: Vec<common::Token>,
    /// Protocols involved in the bundle
    pub protocols_involved: Vec<common::Protocol>,
    /// Estimated computational complexity
    pub complexity_estimate: ComplexityEstimate,
    /// Whether the bundle has cross-chain operations
    pub has_cross_chain: bool,
    /// Whether the bundle has parallel operations
    pub has_parallel: bool,
}

/// Estimate of computational complexity for the bundle
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComplexityEstimate {
    /// Time complexity class
    pub time_complexity: String,
    /// Space complexity estimate
    pub space_complexity: String,
    /// Estimated execution time in microseconds
    pub estimated_time_us: u64,
    /// Estimated memory usage in bytes
    pub estimated_memory_bytes: u64,
}

impl AnalysisResult {
    /// Create a full match result
    pub fn full_match(
        pattern_match: PatternMatch,
        theorem_reference: String,
        safety_guarantees: Vec<SafetyProperty>,
    ) -> Self {
        Self::FullMatch {
            pattern_match,
            theorem_reference,
            confidence: 1.0,
            safety_guarantees,
            analysis_id: Uuid::new_v4(),
        }
    }
    
    /// Create a partial match result
    pub fn partial_match(
        pattern_match: PatternMatch,
        confidence: f64,
        validated_properties: Vec<SafetyProperty>,
        missing_guarantees: Vec<SafetyProperty>,
        recommendation: ValidationRecommendation,
    ) -> Self {
        Self::PartialMatch {
            pattern_match,
            confidence,
            validated_properties,
            missing_guarantees,
            recommendation,
            analysis_id: Uuid::new_v4(),
        }
    }
    
    /// Create a heuristic result
    pub fn heuristic(
        risk_assessment: RiskProfile,
        confidence: f64,
        detected_patterns: Vec<String>,
        safety_warnings: Vec<String>,
        manual_review_required: bool,
    ) -> Self {
        Self::Heuristic {
            risk_assessment,
            confidence,
            detected_patterns,
            safety_warnings,
            manual_review_required,
            analysis_id: Uuid::new_v4(),
        }
    }
    
    /// Create a rejection result
    pub fn reject(
        error: ValidationError,
        bundle_hash: String,
        analyzed_properties: BundleAnalysis,
        suggested_fixes: Vec<String>,
    ) -> Self {
        Self::Reject {
            error,
            bundle_hash,
            analyzed_properties,
            suggested_fixes,
            analysis_id: Uuid::new_v4(),
        }
    }
    
    /// Get the confidence score for any result type
    pub fn confidence(&self) -> f64 {
        match self {
            Self::FullMatch { confidence, .. } => *confidence,
            Self::PartialMatch { confidence, .. } => *confidence,
            Self::Heuristic { confidence, .. } => *confidence,
            Self::Reject { .. } => 0.0,
        }
    }
    
    /// Get the analysis ID for any result type
    pub fn analysis_id(&self) -> Uuid {
        match self {
            Self::FullMatch { analysis_id, .. } => *analysis_id,
            Self::PartialMatch { analysis_id, .. } => *analysis_id,
            Self::Heuristic { analysis_id, .. } => *analysis_id,
            Self::Reject { analysis_id, .. } => *analysis_id,
        }
    }
    
    /// Check if the result indicates the bundle should be executed
    pub fn should_execute(&self) -> bool {
        match self {
            Self::FullMatch { .. } => true,
            Self::PartialMatch { recommendation, .. } => {
                matches!(recommendation, ValidationRecommendation::ProceedWithCaution)
            }
            Self::Heuristic { risk_assessment, .. } => {
                matches!(risk_assessment.recommendation, RiskRecommendation::LowRisk)
            }
            Self::Reject { .. } => false,
        }
    }
    
    /// Get safety properties guaranteed by this result
    pub fn safety_guarantees(&self) -> Vec<SafetyProperty> {
        match self {
            Self::FullMatch { safety_guarantees, .. } => safety_guarantees.clone(),
            Self::PartialMatch { validated_properties, .. } => validated_properties.clone(),
            Self::Heuristic { .. } => vec![], // No guarantees for heuristic results
            Self::Reject { .. } => vec![],
        }
    }
}

impl RiskProfile {
    /// Create a new risk profile
    pub fn new(
        overall_score: f64,
        risk_factors: Vec<RiskFactor>,
        confidence: f64,
    ) -> Self {
        let recommendation = match overall_score {
            score if score < 0.2 => RiskRecommendation::LowRisk,
            score if score < 0.5 => RiskRecommendation::MediumRisk,
            score if score < 0.8 => RiskRecommendation::HighRisk,
            _ => RiskRecommendation::UnacceptableRisk,
        };
        
        Self {
            overall_score,
            risk_factors,
            confidence,
            recommendation,
        }
    }
    
    /// Check if the risk profile indicates high risk
    pub fn is_high_risk(&self) -> bool {
        matches!(
            self.recommendation,
            RiskRecommendation::HighRisk | RiskRecommendation::UnacceptableRisk
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::pattern_types::{ProvenPattern, PatternTemplate, SafetyProperty, ComplexityClass};

    #[test]
    fn test_analysis_result_confidence() {
        let pattern = ProvenPattern::new(
            "test".to_string(),
            "Test".to_string(),
            "test.theorem".to_string(),
            PatternTemplate::Wildcard,
            vec![SafetyProperty::Atomic],
            ComplexityClass::Constant,
        );
        
        let pattern_match = PatternMatch::new(
            pattern,
            1.0,
            HashMap::new(),
            vec![SafetyProperty::Atomic],
        );
        
        let result = AnalysisResult::full_match(
            pattern_match,
            "test.theorem".to_string(),
            vec![SafetyProperty::Atomic],
        );
        
        assert_eq!(result.confidence(), 1.0);
        assert!(result.should_execute());
        assert_eq!(result.safety_guarantees(), vec![SafetyProperty::Atomic]);
    }

    #[test]
    fn test_risk_profile_creation() {
        let risk_factors = vec![
            RiskFactor::HighComplexity(0.3),
            RiskFactor::UnknownActions(vec!["unknown_action".to_string()]),
        ];
        
        let risk_profile = RiskProfile::new(0.3, risk_factors, 0.8);
        
        assert_eq!(risk_profile.overall_score, 0.3);
        assert!(!risk_profile.is_high_risk());
        assert!(matches!(risk_profile.recommendation, RiskRecommendation::MediumRisk));
    }
}