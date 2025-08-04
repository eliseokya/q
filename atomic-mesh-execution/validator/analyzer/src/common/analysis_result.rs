//! Analysis result types for the tiered fallback system

use serde::{Deserialize, Serialize};
use uuid::Uuid;
use super::pattern_types::SafetyProperty;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AnalysisResult {
    FullMatch {
        theorem_reference: String,
        confidence: f64,
        safety_guarantees: Vec<SafetyProperty>,
        gas_optimization_available: bool,
        execution_plan: String,
    },
    PartialMatch {
        theorem_reference: String,
        confidence: f64,
        validated_properties: Vec<SafetyProperty>,
        missing_guarantees: Vec<SafetyProperty>,
        recommendation: ValidationRecommendation,
    },
    Heuristic {
        risk_assessment: RiskProfile,
        confidence: f64,
        detected_patterns: Vec<String>,
        safety_warnings: Vec<String>,
        manual_review_required: bool,
        analysis_id: Uuid,
    },
    Reject {
        error: ValidationError,
        bundle_hash: String,
        analyzed_properties: BundleAnalysis,
        suggested_fixes: Vec<String>,
        analysis_id: Uuid,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ValidationRecommendation {
    ProceedWithCaution,
    RequireAdditionalValidation,
    RecommendManualReview,
    SuggestModifications(Vec<String>),
    Reject(String),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RiskProfile {
    pub overall_score: f64,
    pub risk_factors: Vec<RiskFactor>,
    pub confidence: f64,
    pub recommendation: RiskRecommendation,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RiskFactor {
    HighComplexity(f64),
    UnknownActions(Vec<String>),
    CrossChainUnsafe(String),
    GasRisk(String),
    TimingRisk(String),
    BalanceRisk(String),
    InvariantRisk(String),
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum RiskRecommendation {
    LowRisk,
    MediumRisk,
    HighRisk,
    UnacceptableRisk,
}

#[derive(Debug, Clone, Serialize, Deserialize, thiserror::Error)]
pub enum ValidationError {
    #[error("No matching pattern found for bundle structure")]
    UnknownPattern,
    #[error("Bundle violates constraint: {constraint}")]
    ConstraintViolation { constraint: String },
    #[error("Analysis timed out after {timeout_ms}ms")]
    PerformanceTimeout { timeout_ms: u64 },
    #[error("Malformed bundle structure: {details}")]
    MalformedBundle { details: String },
    #[error("Mathematical invariant violation: {invariant}")]
    InvariantViolation { invariant: String },
    #[error("Cross-chain safety violation: {details}")]
    CrossChainSafetyViolation { details: String },
    #[error("Internal analyzer error: {details}")]
    InternalError { details: String },
    #[error("Pattern load error: {details}")]
    PatternLoadError { details: String },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BundleAnalysis {
    pub action_count: usize,
    pub chains_involved: Vec<common::Chain>,
    pub tokens_involved: Vec<common::Token>,
    pub protocols_involved: Vec<common::Protocol>,
    pub complexity_estimate: ComplexityEstimate,
    pub has_cross_chain: bool,
    pub has_parallel: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComplexityEstimate {
    pub time_complexity: String,
    pub space_complexity: String,
    pub estimated_time_us: u64,
    pub estimated_memory_bytes: u64,
}

impl RiskProfile {
    pub fn new(overall_score: f64, risk_factors: Vec<RiskFactor>, confidence: f64) -> Self {
        let recommendation = match overall_score {
            score if score < 0.2 => RiskRecommendation::LowRisk,
            score if score < 0.5 => RiskRecommendation::MediumRisk,
            score if score < 0.8 => RiskRecommendation::HighRisk,
            _ => RiskRecommendation::UnacceptableRisk,
        };
        
        Self { overall_score, risk_factors, confidence, recommendation }
    }
}

impl AnalysisResult {
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
}
