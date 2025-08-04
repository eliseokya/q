//! Confidence calculation for pattern matches
//! 
//! This module implements mathematical confidence scoring based on:
//! - Perfect matches with proven theorems: confidence = 1.0
//! - Structural matches with heuristic validation: confidence = 0.5-0.95
//! - Risk-based scoring for unknown patterns: confidence = 0.1-0.5

use crate::common::pattern_types::{ProvenPattern, PatternCandidate, SafetyProperty};
use crate::common::analysis_result::RiskProfile;
use common::types::{Bundle, Expr, Action};
use std::collections::HashSet;

/// Confidence calculator for pattern matches
pub struct ConfidenceCalculator {
    /// Base confidence for structural matches
    structural_match_base: f64,
    /// Confidence boost per verified safety property
    property_boost: f64,
    /// Maximum confidence without full proof
    max_heuristic_confidence: f64,
}

impl Default for ConfidenceCalculator {
    fn default() -> Self {
        Self {
            structural_match_base: 0.5,
            property_boost: 0.05,
            max_heuristic_confidence: 0.95,
        }
    }
}

impl ConfidenceCalculator {
    pub fn new() -> Self {
        Self::default()
    }
    
    /// Calculate confidence score for a pattern match with full theorem proof
    pub fn calculate_proven_confidence(
        &self,
        pattern: &ProvenPattern,
        theorem_verified: bool,
        verified_properties: &[SafetyProperty],
    ) -> f64 {
        if theorem_verified && self.all_properties_verified(pattern, verified_properties) {
            // Perfect match with all properties verified
            1.0
        } else if theorem_verified {
            // Theorem verified but missing some properties
            0.9 + (verified_properties.len() as f64 * 0.01)
        } else {
            // No theorem verification
            self.calculate_heuristic_confidence(pattern, verified_properties)
        }
    }
    
    /// Calculate confidence for structural matches without full proof
    pub fn calculate_heuristic_confidence(
        &self,
        pattern: &ProvenPattern,
        verified_properties: &[SafetyProperty],
    ) -> f64 {
        let mut confidence = self.structural_match_base;
        
        // Boost confidence for each verified property
        confidence += verified_properties.len() as f64 * self.property_boost;
        
        // Apply pattern-specific adjustments
        confidence *= self.pattern_complexity_factor(pattern);
        
        // Cap at maximum heuristic confidence
        confidence.min(self.max_heuristic_confidence)
    }
    
    /// Calculate confidence for unknown patterns based on risk assessment
    pub fn calculate_risk_based_confidence(
        &self,
        risk_profile: &RiskProfile,
        detected_pattern_similarity: f64,
    ) -> f64 {
        // Base confidence inversely proportional to risk
        let risk_factor = 1.0 - risk_profile.overall_score;
        
        // Adjust for pattern similarity (0.0 to 1.0)
        let similarity_factor = detected_pattern_similarity;
        
        // Combine factors
        let confidence = 0.1 + (risk_factor * 0.2) + (similarity_factor * 0.2);
        
        // Ensure within bounds [0.1, 0.5]
        confidence.max(0.1).min(0.5)
    }
    
    /// Adjust confidence based on bundle characteristics
    pub fn adjust_confidence_for_bundle(
        &self,
        base_confidence: f64,
        bundle: &Bundle,
    ) -> f64 {
        let mut adjusted = base_confidence;
        
        // Reduce confidence for complex bundles
        let complexity = self.calculate_bundle_complexity(bundle);
        if complexity > 10 {
            adjusted *= 0.9;
        }
        
        // Reduce confidence for cross-chain operations
        if self.is_cross_chain_bundle(bundle) {
            adjusted *= 0.95;
        }
        
        // Reduce confidence for high gas operations
        if self.has_high_gas_risk(bundle) {
            adjusted *= 0.9;
        }
        
        adjusted.max(0.1) // Never go below 0.1
    }
    
    /// Create a confidence-enhanced pattern candidate
    pub fn enhance_pattern_candidate(
        &self,
        mut candidate: PatternCandidate,
        theorem_verified: bool,
        verified_properties: Vec<SafetyProperty>,
    ) -> PatternCandidate {
        // Calculate final confidence score
        let confidence = if theorem_verified {
            self.calculate_proven_confidence(
                &candidate.pattern,
                theorem_verified,
                &verified_properties,
            )
        } else {
            self.calculate_heuristic_confidence(
                &candidate.pattern,
                &verified_properties,
            )
        };
        
        // Update the candidate
        candidate.confidence_score = confidence;
        candidate.semantic_match = theorem_verified;
        
        candidate
    }
    
    // Helper methods
    
    fn all_properties_verified(
        &self,
        pattern: &ProvenPattern,
        verified: &[SafetyProperty],
    ) -> bool {
        let verified_set: HashSet<_> = verified.iter().collect();
        pattern.safety_properties.iter().all(|p| verified_set.contains(p))
    }
    
    fn pattern_complexity_factor(&self, pattern: &ProvenPattern) -> f64 {
        use crate::common::pattern_types::PatternTemplate;
        
        match pattern.pattern_template {
            PatternTemplate::FlashLoan => 1.0,          // Well-understood pattern
            PatternTemplate::TriangularArbitrage => 0.95,
            PatternTemplate::CrossChainArbitrage => 0.9, // More complex
            PatternTemplate::LiquidityMigration => 0.85,
            PatternTemplate::BridgeOperation => 0.8,
            PatternTemplate::ProtocolSpecific => 0.7,    // Depends on protocol
            _ => 0.6,                                     // Unknown complexity
        }
    }
    
    fn calculate_bundle_complexity(&self, bundle: &Bundle) -> usize {
        // Count total operations in the bundle
        self.count_operations(&bundle.expr)
    }
    
    fn count_operations(&self, expr: &Expr) -> usize {
        match expr {
            Expr::Action { .. } => 1,
            Expr::Seq { first, second } => {
                self.count_operations(first) + self.count_operations(second)
            }
            Expr::Parallel { exprs } => {
                exprs.iter().map(|e| self.count_operations(e)).sum()
            }
            Expr::OnChain { expr, .. } => self.count_operations(expr),
        }
    }
    
    fn is_cross_chain_bundle(&self, bundle: &Bundle) -> bool {
        // Check if bundle involves multiple chains
        self.count_chains(&bundle.expr) > 1
    }
    
    fn count_chains(&self, expr: &Expr) -> usize {
        let mut chains = HashSet::new();
        self.collect_chains(expr, &mut chains);
        chains.len()
    }
    
    fn collect_chains(&self, expr: &Expr, chains: &mut HashSet<String>) {
        match expr {
            Expr::Action { action } => {
                if let Action::Bridge { chain, .. } = action {
                    chains.insert(format!("{:?}", chain));
                }
            }
            Expr::Seq { first, second } => {
                self.collect_chains(first, chains);
                self.collect_chains(second, chains);
            }
            Expr::Parallel { exprs } => {
                for e in exprs {
                    self.collect_chains(e, chains);
                }
            }
            Expr::OnChain { chain, expr } => {
                chains.insert(format!("{:?}", chain));
                self.collect_chains(expr, chains);
            }
        }
    }
    
    fn has_high_gas_risk(&self, bundle: &Bundle) -> bool {
        // Check if bundle has high gas constraints
        bundle.constraints.iter().any(|c| {
            if let common::types::Constraint::MaxGas { amount } = c {
                *amount > 1_000_000
            } else {
                false
            }
        })
    }
}

/// Confidence scoring configuration
pub struct ConfidenceConfig {
    /// Minimum confidence required for execution
    pub min_execution_confidence: f64,
    /// Confidence threshold for manual review
    pub manual_review_threshold: f64,
    /// Confidence boost for gas optimization
    pub gas_optimization_boost: f64,
}

impl Default for ConfidenceConfig {
    fn default() -> Self {
        Self {
            min_execution_confidence: 0.7,
            manual_review_threshold: 0.5,
            gas_optimization_boost: 0.05,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_perfect_match_confidence() {
        let calculator = ConfidenceCalculator::new();
        let pattern = create_test_pattern();
        
        let confidence = calculator.calculate_proven_confidence(
            &pattern,
            true,
            &pattern.safety_properties,
        );
        
        assert_eq!(confidence, 1.0);
    }
    
    #[test]
    fn test_heuristic_confidence_bounds() {
        let calculator = ConfidenceCalculator::new();
        let pattern = create_test_pattern();
        
        let confidence = calculator.calculate_heuristic_confidence(
            &pattern,
            &[SafetyProperty::Atomicity],
        );
        
        assert!(confidence >= 0.5);
        assert!(confidence <= 0.95);
    }
    
    #[test]
    fn test_risk_based_confidence_bounds() {
        let calculator = ConfidenceCalculator::new();
        let risk_profile = RiskProfile {
            overall_score: 0.3,
            risk_factors: vec![],
            confidence: 0.5,
            recommendation: crate::common::analysis_result::RiskRecommendation::MediumRisk,
        };
        
        let confidence = calculator.calculate_risk_based_confidence(
            &risk_profile,
            0.6,
        );
        
        assert!(confidence >= 0.1);
        assert!(confidence <= 0.5);
    }
    
    fn create_test_pattern() -> ProvenPattern {
        ProvenPattern {
            pattern_id: "test".to_string(),
            pattern_template: crate::common::pattern_types::PatternTemplate::FlashLoan,
            theorem_reference: "FlashLoanPattern".to_string(),
            theorem_file: std::path::PathBuf::from("test.lean"),
            theorem_line: 1,
            safety_properties: vec![SafetyProperty::Atomicity],
            preconditions: vec!["amount > 0".to_string()],
            structure_regex: ".*".to_string(),
            confidence_threshold: 0.7,
            gas_optimization_potential: true,
        }
    }
}