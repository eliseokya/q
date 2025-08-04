//! Result builder for constructing tiered analysis results
//! 
//! This module provides builder patterns to simplify creating complex
//! analysis results with proper fallback handling.

use super::analysis_result::*;
use crate::common::pattern_types::{ProvenPattern, SafetyProperty, PatternCandidate};
use crate::semantic::theorem_engine::TheoremError;
use std::collections::HashMap;

/// Builder for constructing analysis results with fallback logic
pub struct ResultBuilder {
    pattern_candidates: Vec<PatternCandidate>,
    theorem_results: HashMap<String, Result<Vec<SafetyProperty>, TheoremError>>,
    structural_matches: Vec<(String, f64)>, // (structure_description, similarity)
    risk_factors: Vec<String>,
    warnings: Vec<String>,
    rejection_reasons: Vec<RejectionReason>,
}

impl ResultBuilder {
    pub fn new() -> Self {
        Self {
            pattern_candidates: Vec::new(),
            theorem_results: HashMap::new(),
            structural_matches: Vec::new(),
            risk_factors: Vec::new(),
            warnings: Vec::new(),
            rejection_reasons: Vec::new(),
        }
    }
    
    /// Add pattern match candidates
    pub fn with_pattern_candidates(mut self, candidates: Vec<PatternCandidate>) -> Self {
        self.pattern_candidates = candidates;
        self
    }
    
    /// Add theorem validation results
    pub fn with_theorem_results(
        mut self, 
        results: HashMap<String, Result<Vec<SafetyProperty>, TheoremError>>
    ) -> Self {
        self.theorem_results = results;
        self
    }
    
    /// Add structural match information
    pub fn with_structural_match(mut self, structure: String, similarity: f64) -> Self {
        self.structural_matches.push((structure, similarity));
        self
    }
    
    /// Add risk factor
    pub fn add_risk_factor(mut self, risk: String) -> Self {
        self.risk_factors.push(risk);
        self
    }
    
    /// Add warning
    pub fn add_warning(mut self, warning: String) -> Self {
        self.warnings.push(warning);
        self
    }
    
    /// Add rejection reason
    pub fn add_rejection_reason(mut self, reason: RejectionReason) -> Self {
        self.rejection_reasons.push(reason);
        self
    }
    
    /// Build the final analysis result using tiered fallback
    pub fn build(self) -> AnalysisResult {
        // Try for full match first
        if let Some(full_match) = self.try_build_full_match() {
            return full_match;
        }
        
        // Try for partial match
        if let Some(partial_match) = self.try_build_partial_match() {
            return partial_match;
        }
        
        // Try heuristic analysis
        if let Some(heuristic) = self.try_build_heuristic() {
            return heuristic;
        }
        
        // Build rejection with detailed feedback
        self.build_rejection()
    }
    
    fn try_build_full_match(&self) -> Option<AnalysisResult> {
        // Look for pattern with successful theorem validation
        for candidate in &self.pattern_candidates {
            if candidate.confidence_score >= 0.95 {
                if let Some(Ok(safety_guarantees)) = self.theorem_results.get(&candidate.pattern.theorem_reference) {
                    return Some(AnalysisResult::FullMatch {
                        pattern: candidate.pattern.clone(),
                        theorem_reference: candidate.pattern.theorem_reference.clone(),
                        confidence: 1.0,
                        safety_guarantees: safety_guarantees.clone(),
                        gas_optimization_available: candidate.pattern.gas_optimization_potential,
                        execution_plan: format!("Execute using proven pattern {}", candidate.pattern.pattern_id),
                        proof_certificate: self.generate_proof_certificate(&candidate.pattern),
                    });
                }
            }
        }
        None
    }
    
    fn try_build_partial_match(&self) -> Option<AnalysisResult> {
        // Look for high structural similarity with some validation
        if let Some((structure, similarity)) = self.structural_matches.iter()
            .find(|(_, sim)| *sim >= 0.7) 
        {
            let mut validated_properties = Vec::new();
            let mut unverified_properties = Vec::new();
            
            // Collect validated vs unverified properties
            for candidate in &self.pattern_candidates {
                if let Some(result) = self.theorem_results.get(&candidate.pattern.theorem_reference) {
                    match result {
                        Ok(properties) => validated_properties.extend(properties.iter().cloned()),
                        Err(_) => {
                            unverified_properties.extend(candidate.pattern.safety_properties.iter().cloned());
                        }
                    }
                }
            }
            
            // Calculate confidence based on validation ratio
            let total_properties = validated_properties.len() + unverified_properties.len();
            let validation_ratio = if total_properties > 0 {
                validated_properties.len() as f64 / total_properties as f64
            } else {
                0.5
            };
            
            let confidence = 0.5 + (validation_ratio * 0.45); // 0.5-0.95 range
            
            return Some(AnalysisResult::PartialMatch {
                pattern_similarity: *similarity,
                matched_structure: structure.clone(),
                validated_properties,
                unverified_properties,
                confidence,
                risk_factors: self.risk_factors.clone(),
                execution_plan: format!("Execute with monitoring for {} structure", structure),
                warnings: self.warnings.clone(),
            });
        }
        None
    }
    
    fn try_build_heuristic(&self) -> Option<AnalysisResult> {
        // If we have some structural understanding but low confidence
        if !self.structural_matches.is_empty() || !self.pattern_candidates.is_empty() {
            let pattern_type = self.detect_pattern_type();
            let risk_assessment = self.assess_risk();
            let safety_analysis = self.analyze_safety_heuristically();
            
            let confidence = 0.1 + (safety_analysis.confidence_average() * 0.4); // 0.1-0.5 range
            
            let recommended_action = match risk_assessment.overall_risk {
                RiskLevel::Low => RecommendedAction::ExecuteWithMonitoring,
                RiskLevel::Medium => RecommendedAction::ExecuteWithSafeguards {
                    safeguards: vec![
                        "Enable emergency pause".to_string(),
                        "Set strict slippage limits".to_string(),
                        "Monitor for front-running".to_string(),
                    ],
                },
                RiskLevel::High | RiskLevel::Critical => RecommendedAction::RequireManualApproval,
            };
            
            return Some(AnalysisResult::Heuristic {
                pattern_type,
                confidence,
                risk_assessment,
                safety_analysis,
                recommended_action,
                manual_review_required: confidence < 0.3,
                execution_plan: if confidence >= 0.3 {
                    Some("Execute with comprehensive monitoring and safeguards".to_string())
                } else {
                    None
                },
            });
        }
        None
    }
    
    fn build_rejection(&self) -> AnalysisResult {
        let suggested_fixes = self.generate_suggested_fixes();
        let partial_analysis = self.perform_partial_analysis();
        let safety_report = self.generate_safety_report();
        
        AnalysisResult::Reject {
            reasons: if self.rejection_reasons.is_empty() {
                vec![RejectionReason::MalformedStructure {
                    details: "Unable to match any known pattern or perform meaningful analysis".to_string()
                }]
            } else {
                self.rejection_reasons.clone()
            },
            suggested_fixes,
            partial_analysis,
            safety_report,
        }
    }
    
    fn detect_pattern_type(&self) -> String {
        if !self.pattern_candidates.is_empty() {
            return format!("{:?}", self.pattern_candidates[0].pattern.pattern_template);
        }
        if !self.structural_matches.is_empty() {
            return self.structural_matches[0].0.clone();
        }
        "Unknown".to_string()
    }
    
    fn assess_risk(&self) -> RiskAssessment {
        let mut risk_factors = HashMap::new();
        let mut overall_score = 0.0;
        
        // Assess various risk factors
        if self.risk_factors.iter().any(|r| r.contains("cross-chain")) {
            risk_factors.insert("cross_chain_complexity".to_string(), 0.3);
            overall_score += 0.3;
        }
        
        if self.risk_factors.iter().any(|r| r.contains("unknown protocol")) {
            risk_factors.insert("protocol_risk".to_string(), 0.4);
            overall_score += 0.4;
        }
        
        if self.warnings.len() > 3 {
            risk_factors.insert("multiple_warnings".to_string(), 0.2);
            overall_score += 0.2;
        }
        
        let overall_risk = match overall_score {
            s if s < 0.3 => RiskLevel::Low,
            s if s < 0.6 => RiskLevel::Medium,
            s if s < 0.8 => RiskLevel::High,
            _ => RiskLevel::Critical,
        };
        
        RiskAssessment {
            overall_risk,
            risk_factors,
            mitigation_strategies: vec![
                "Implement circuit breakers".to_string(),
                "Add monitoring alerts".to_string(),
                "Use conservative parameters".to_string(),
            ],
            confidence_in_assessment: 0.7,
        }
    }
    
    fn analyze_safety_heuristically(&self) -> SafetyAnalysis {
        let mut confidence_per_property = HashMap::new();
        
        // Basic heuristic checks
        let balance_preserved = if self.risk_factors.iter().any(|r| r.contains("balance")) {
            Some(false)
        } else {
            Some(true)
        };
        confidence_per_property.insert(SafetyProperty::BalancePreservation, 0.6);
        
        let atomicity_likely = self.pattern_candidates.iter()
            .any(|c| c.pattern.safety_properties.contains(&SafetyProperty::Atomicity));
        confidence_per_property.insert(SafetyProperty::Atomicity, 0.5);
        
        SafetyAnalysis {
            balance_preserved,
            atomicity_likely: Some(atomicity_likely),
            revert_safe: Some(true), // Assume revert safety by default
            value_extraction_risk: Some(0.2),
            confidence_per_property,
        }
    }
    
    fn generate_suggested_fixes(&self) -> Vec<SuggestedFix> {
        let mut fixes = Vec::new();
        
        for reason in &self.rejection_reasons {
            match reason {
                RejectionReason::InsufficientLiquidity { .. } => {
                    fixes.push(SuggestedFix {
                        fix_type: FixType::AdjustAmount,
                        description: "Reduce transaction amount to match available liquidity".to_string(),
                        estimated_impact: "Lower profit but higher success rate".to_string(),
                    });
                }
                RejectionReason::UnsupportedProtocol { protocol } => {
                    fixes.push(SuggestedFix {
                        fix_type: FixType::ChangeProtocol,
                        description: format!("Switch from {} to a supported protocol", protocol),
                        estimated_impact: "May require different parameters".to_string(),
                    });
                }
                RejectionReason::TimingConflict { .. } => {
                    fixes.push(SuggestedFix {
                        fix_type: FixType::AddBridge,
                        description: "Add intermediate bridge to resolve timing issues".to_string(),
                        estimated_impact: "Additional gas costs but enables execution".to_string(),
                    });
                }
                _ => {}
            }
        }
        
        fixes
    }
    
    fn perform_partial_analysis(&self) -> Option<PartialAnalysis> {
        if self.pattern_candidates.is_empty() && self.structural_matches.is_empty() {
            return None;
        }
        
        Some(PartialAnalysis {
            valid_segments: vec!["Initial state valid".to_string()],
            problematic_segments: self.risk_factors.clone(),
            salvageable: !self.rejection_reasons.iter().any(|r| {
                matches!(r, RejectionReason::SafetyViolation { .. })
            }),
            modification_suggestions: vec![
                "Simplify bundle structure".to_string(),
                "Use well-known patterns".to_string(),
            ],
        })
    }
    
    fn generate_safety_report(&self) -> SafetyReport {
        SafetyReport {
            atomicity_analysis: "Atomicity cannot be guaranteed without pattern match".to_string(),
            balance_analysis: "Balance preservation uncertain".to_string(),
            protocol_safety: HashMap::new(),
            cross_chain_risks: self.risk_factors.iter()
                .filter(|r| r.contains("cross-chain"))
                .cloned()
                .collect(),
            overall_safety_score: 0.3, // Low score for rejected bundles
        }
    }
    
    fn generate_proof_certificate(&self, pattern: &ProvenPattern) -> String {
        format!("PROOF[{}:{}:{}]", 
            pattern.theorem_file.display(),
            pattern.theorem_line,
            pattern.theorem_reference
        )
    }
    
    fn try_build_full_match(&self) -> Option<AnalysisResult> {
        // Look for pattern with successful theorem validation
        for candidate in &self.pattern_candidates {
            if candidate.confidence_score >= 0.95 {
                if let Some(Ok(safety_guarantees)) = self.theorem_results.get(&candidate.pattern.theorem_reference) {
                    return Some(AnalysisResult::FullMatch {
                        pattern: candidate.pattern.clone(),
                        theorem_reference: candidate.pattern.theorem_reference.clone(),
                        confidence: 1.0,
                        safety_guarantees: safety_guarantees.clone(),
                        gas_optimization_available: candidate.pattern.gas_optimization_potential,
                        execution_plan: format!("Execute using proven pattern {}", candidate.pattern.pattern_id),
                        proof_certificate: self.generate_proof_certificate(&candidate.pattern),
                    });
                }
            }
        }
        None
    }
    
    fn try_build_partial_match(&self) -> Option<AnalysisResult> {
        // Look for high structural similarity with some validation
        if let Some((structure, similarity)) = self.structural_matches.iter()
            .find(|(_, sim)| *sim >= 0.7) 
        {
            let mut validated_properties = Vec::new();
            let mut unverified_properties = Vec::new();
            
            // Collect validated vs unverified properties
            for candidate in &self.pattern_candidates {
                if let Some(result) = self.theorem_results.get(&candidate.pattern.theorem_reference) {
                    match result {
                        Ok(properties) => validated_properties.extend(properties.iter().cloned()),
                        Err(_) => {
                            unverified_properties.extend(candidate.pattern.safety_properties.iter().cloned());
                        }
                    }
                }
            }
            
            // Calculate confidence based on validation ratio
            let total_properties = validated_properties.len() + unverified_properties.len();
            let validation_ratio = if total_properties > 0 {
                validated_properties.len() as f64 / total_properties as f64
            } else {
                0.5
            };
            
            let confidence = 0.5 + (validation_ratio * 0.45); // 0.5-0.95 range
            
            return Some(AnalysisResult::PartialMatch {
                pattern_similarity: *similarity,
                matched_structure: structure.clone(),
                validated_properties,
                unverified_properties,
                confidence,
                risk_factors: self.risk_factors.clone(),
                execution_plan: format!("Execute with monitoring for {} structure", structure),
                warnings: self.warnings.clone(),
            });
        }
        None
    }
    
    fn try_build_heuristic(&self) -> Option<AnalysisResult> {
        // If we have some structural understanding but low confidence
        if !self.structural_matches.is_empty() || !self.pattern_candidates.is_empty() {
            let pattern_type = self.detect_pattern_type();
            let risk_assessment = self.assess_risk();
            let safety_analysis = self.analyze_safety_heuristically();
            
            let confidence = 0.1 + (safety_analysis.confidence_average() * 0.4); // 0.1-0.5 range
            
            let recommended_action = match risk_assessment.overall_risk {
                RiskLevel::Low => RecommendedAction::ExecuteWithMonitoring,
                RiskLevel::Medium => RecommendedAction::ExecuteWithSafeguards {
                    safeguards: vec![
                        "Enable emergency pause".to_string(),
                        "Set strict slippage limits".to_string(),
                        "Monitor for front-running".to_string(),
                    ],
                },
                RiskLevel::High | RiskLevel::Critical => RecommendedAction::RequireManualApproval,
            };
            
            return Some(AnalysisResult::Heuristic {
                pattern_type,
                confidence,
                risk_assessment,
                safety_analysis,
                recommended_action,
                manual_review_required: confidence < 0.3,
                execution_plan: if confidence >= 0.3 {
                    Some("Execute with comprehensive monitoring and safeguards".to_string())
                } else {
                    None
                },
            });
        }
        None
    }
    
    fn build_rejection(&self) -> AnalysisResult {
        let suggested_fixes = self.generate_suggested_fixes();
        let partial_analysis = self.perform_partial_analysis();
        let safety_report = self.generate_safety_report();
        
        AnalysisResult::Reject {
            reasons: if self.rejection_reasons.is_empty() {
                vec![RejectionReason::MalformedStructure {
                    details: "Unable to match any known pattern or perform meaningful analysis".to_string()
                }]
            } else {
                self.rejection_reasons.clone()
            },
            suggested_fixes,
            partial_analysis,
            safety_report,
        }
    }
    
    fn detect_pattern_type(&self) -> String {
        if !self.pattern_candidates.is_empty() {
            return format!("{:?}", self.pattern_candidates[0].pattern.pattern_template);
        }
        if !self.structural_matches.is_empty() {
            return self.structural_matches[0].0.clone();
        }
        "Unknown".to_string()
    }
    
    fn assess_risk(&self) -> RiskAssessment {
        let mut risk_factors = HashMap::new();
        let mut overall_score = 0.0;
        
        // Assess various risk factors
        if self.risk_factors.iter().any(|r| r.contains("cross-chain")) {
            risk_factors.insert("cross_chain_complexity".to_string(), 0.3);
            overall_score += 0.3;
        }
        
        if self.risk_factors.iter().any(|r| r.contains("unknown protocol")) {
            risk_factors.insert("protocol_risk".to_string(), 0.4);
            overall_score += 0.4;
        }
        
        if self.warnings.len() > 3 {
            risk_factors.insert("multiple_warnings".to_string(), 0.2);
            overall_score += 0.2;
        }
        
        let overall_risk = match overall_score {
            s if s < 0.3 => RiskLevel::Low,
            s if s < 0.6 => RiskLevel::Medium,
            s if s < 0.8 => RiskLevel::High,
            _ => RiskLevel::Critical,
        };
        
        RiskAssessment {
            overall_risk,
            risk_factors,
            mitigation_strategies: vec![
                "Implement circuit breakers".to_string(),
                "Add monitoring alerts".to_string(),
                "Use conservative parameters".to_string(),
            ],
            confidence_in_assessment: 0.7,
        }
    }
    
    fn analyze_safety_heuristically(&self) -> SafetyAnalysis {
        let mut confidence_per_property = HashMap::new();
        
        // Basic heuristic checks
        let balance_preserved = if self.risk_factors.iter().any(|r| r.contains("balance")) {
            Some(false)
        } else {
            Some(true)
        };
        confidence_per_property.insert(SafetyProperty::BalancePreservation, 0.6);
        
        let atomicity_likely = self.pattern_candidates.iter()
            .any(|c| c.pattern.safety_properties.contains(&SafetyProperty::Atomicity));
        confidence_per_property.insert(SafetyProperty::Atomicity, 0.5);
        
        SafetyAnalysis {
            balance_preserved,
            atomicity_likely: Some(atomicity_likely),
            revert_safe: Some(true), // Assume revert safety by default
            value_extraction_risk: Some(0.2),
            confidence_per_property,
        }
    }
    
    fn generate_suggested_fixes(&self) -> Vec<SuggestedFix> {
        let mut fixes = Vec::new();
        
        for reason in &self.rejection_reasons {
            match reason {
                RejectionReason::InsufficientLiquidity { .. } => {
                    fixes.push(SuggestedFix {
                        fix_type: FixType::AdjustAmount,
                        description: "Reduce transaction amount to match available liquidity".to_string(),
                        estimated_impact: "Lower profit but higher success rate".to_string(),
                    });
                }
                RejectionReason::UnsupportedProtocol { protocol } => {
                    fixes.push(SuggestedFix {
                        fix_type: FixType::ChangeProtocol,
                        description: format!("Switch from {} to a supported protocol", protocol),
                        estimated_impact: "May require different parameters".to_string(),
                    });
                }
                RejectionReason::TimingConflict { .. } => {
                    fixes.push(SuggestedFix {
                        fix_type: FixType::AddBridge,
                        description: "Add intermediate bridge to resolve timing issues".to_string(),
                        estimated_impact: "Additional gas costs but enables execution".to_string(),
                    });
                }
                _ => {}
            }
        }
        
        fixes
    }
    
    fn perform_partial_analysis(&self) -> Option<PartialAnalysis> {
        if self.pattern_candidates.is_empty() && self.structural_matches.is_empty() {
            return None;
        }
        
        Some(PartialAnalysis {
            valid_segments: vec!["Initial state valid".to_string()],
            problematic_segments: self.risk_factors.clone(),
            salvageable: !self.rejection_reasons.iter().any(|r| {
                matches!(r, RejectionReason::SafetyViolation { .. })
            }),
            modification_suggestions: vec![
                "Simplify bundle structure".to_string(),
                "Use well-known patterns".to_string(),
            ],
        })
    }
    
    fn generate_safety_report(&self) -> SafetyReport {
        SafetyReport {
            atomicity_analysis: "Atomicity cannot be guaranteed without pattern match".to_string(),
            balance_analysis: "Balance preservation uncertain".to_string(),
            protocol_safety: HashMap::new(),
            cross_chain_risks: self.risk_factors.iter()
                .filter(|r| r.contains("cross-chain"))
                .cloned()
                .collect(),
            overall_safety_score: 0.3, // Low score for rejected bundles
        }
    }
    
    fn generate_proof_certificate(&self, pattern: &ProvenPattern) -> String {
        format!("PROOF[{}:{}:{}]", 
            pattern.theorem_file.display(),
            pattern.theorem_line,
            pattern.theorem_reference
        )
    }
}

impl SafetyAnalysis {
    fn confidence_average(&self) -> f64 {
        if self.confidence_per_property.is_empty() {
            return 0.0;
        }
        
        let sum: f64 = self.confidence_per_property.values().sum();
        sum / self.confidence_per_property.len() as f64
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::pattern_types::PatternTemplate;
    use std::path::PathBuf;
    
    #[test]
    fn test_builder_full_match() {
        let pattern = ProvenPattern {
            pattern_id: "flash-loan-001".to_string(),
            pattern_template: PatternTemplate::FlashLoan,
            theorem_reference: "FlashLoanTheorem".to_string(),
            theorem_file: PathBuf::from("test.lean"),
            theorem_line: 42,
            safety_properties: vec![SafetyProperty::Atomicity],
            preconditions: vec![],
            structure_regex: ".*".to_string(),
            confidence_threshold: 0.7,
            gas_optimization_potential: true,
        };
        
        let candidate = PatternCandidate {
            pattern: pattern.clone(),
            confidence_score: 0.95,
            match_location: (0, 10),
        };
        
        let mut theorem_results = HashMap::new();
        theorem_results.insert(
            "FlashLoanTheorem".to_string(),
            Ok(vec![SafetyProperty::Atomicity])
        );
        
        let result = ResultBuilder::new()
            .with_pattern_candidates(vec![candidate])
            .with_theorem_results(theorem_results)
            .build();
        
        assert!(matches!(result, AnalysisResult::FullMatch { .. }));
        assert_eq!(result.confidence(), 1.0);
        assert!(result.is_executable());
    }
    
    #[test]
    fn test_builder_fallback_to_partial() {
        let result = ResultBuilder::new()
            .with_structural_match("flash-loan-like".to_string(), 0.8)
            .add_risk_factor("Unknown protocol variant".to_string())
            .build();
        
        assert!(matches!(result, AnalysisResult::PartialMatch { .. }));
        assert!(result.confidence() >= 0.5 && result.confidence() <= 0.95);
    }
    
    #[test]
    fn test_builder_rejection() {
        let result = ResultBuilder::new()
            .add_rejection_reason(RejectionReason::SafetyViolation {
                property: SafetyProperty::Atomicity,
                details: "Cannot guarantee atomicity".to_string(),
            })
            .build();
        
        assert!(matches!(result, AnalysisResult::Reject { .. }));
        assert_eq!(result.confidence(), 0.0);
        assert!(!result.is_executable());
    }
}