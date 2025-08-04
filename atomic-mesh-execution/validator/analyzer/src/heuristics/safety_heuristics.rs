//! Safety heuristics for bundle analysis without formal proofs
//! 
//! This module provides heuristic methods to assess bundle safety
//! when mathematical theorems are not available.

use common::types::{Bundle, Action, Token, Protocol};
use crate::common::pattern_types::SafetyProperty;
use crate::fallback::{RejectionReason, SuggestedFix, FixType};
use super::structural_analyzer::{StructuralAnalysis, ActionInfo};
use std::collections::{HashMap, HashSet};
use num_traits::sign::Signed;

/// Safety heuristics engine
pub struct SafetyHeuristics {
    min_liquidity_thresholds: HashMap<Token, u64>,
    max_slippage_tolerance: f64,
    max_gas_per_action: u64,
}

impl SafetyHeuristics {
    pub fn new() -> Self {
        let mut min_liquidity_thresholds = HashMap::new();
        min_liquidity_thresholds.insert(Token::WETH, 100_000_000_000_000_000); // 0.1 ETH
        min_liquidity_thresholds.insert(Token::USDC, 100_000_000); // 100 USDC
        min_liquidity_thresholds.insert(Token::DAI, 100_000_000_000_000_000_000); // 100 DAI
        
        Self {
            min_liquidity_thresholds,
            max_slippage_tolerance: 0.03, // 3% max slippage
            max_gas_per_action: 500_000,
        }
    }
    
    /// Check if bundle likely violates safety properties
    pub fn check_safety_violations(&self, analysis: &StructuralAnalysis) -> Vec<RejectionReason> {
        let mut violations = Vec::new();
        
        // Check for obvious safety violations
        if let Some(atomicity_violation) = self.check_atomicity_violation(analysis) {
            violations.push(atomicity_violation);
        }
        
        if let Some(balance_violation) = self.check_balance_violation(analysis) {
            violations.push(balance_violation);
        }
        
        if let Some(liquidity_violation) = self.check_liquidity_violation(analysis) {
            violations.push(liquidity_violation);
        }
        
        if let Some(timing_violation) = self.check_timing_violation(analysis) {
            violations.push(timing_violation);
        }
        
        violations
    }
    
    /// Generate suggested fixes for safety violations
    pub fn generate_fixes(&self, violations: &[RejectionReason], analysis: &StructuralAnalysis) -> Vec<SuggestedFix> {
        let mut fixes = Vec::new();
        
        for violation in violations {
            match violation {
                RejectionReason::SafetyViolation { property, .. } => {
                    match property {
                        SafetyProperty::Atomicity => {
                            fixes.push(SuggestedFix {
                                fix_type: FixType::SimplifyStructure,
                                description: "Ensure all operations can complete atomically".to_string(),
                                estimated_impact: "May require restructuring bundle logic".to_string(),
                            });
                        }
                        SafetyProperty::BalancePreservation => {
                            fixes.push(SuggestedFix {
                                fix_type: FixType::AdjustAmount,
                                description: "Balance input and output amounts across all operations".to_string(),
                                estimated_impact: "Ensures no value is lost or created".to_string(),
                            });
                        }
                        _ => {}
                    }
                }
                RejectionReason::InsufficientLiquidity { .. } => {
                    fixes.push(SuggestedFix {
                        fix_type: FixType::WaitForLiquidity,
                        description: "Monitor pools and execute when liquidity improves".to_string(),
                        estimated_impact: "Delayed execution but higher success rate".to_string(),
                    });
                }
                RejectionReason::TimingConflict { .. } => {
                    fixes.push(SuggestedFix {
                        fix_type: FixType::SplitBundle,
                        description: "Split into smaller bundles with relaxed timing".to_string(),
                        estimated_impact: "Higher gas costs but more reliable execution".to_string(),
                    });
                }
                _ => {}
            }
        }
        
        fixes
    }
    
    /// Calculate safety confidence for each property
    pub fn calculate_property_confidence(&self, analysis: &StructuralAnalysis) -> HashMap<SafetyProperty, f64> {
        let mut confidence = HashMap::new();
        
        // Atomicity confidence
        let atomicity_score = self.calculate_atomicity_confidence(analysis);
        confidence.insert(SafetyProperty::Atomicity, atomicity_score);
        
        // Balance preservation confidence  
        let balance_score = self.calculate_balance_confidence(analysis);
        confidence.insert(SafetyProperty::BalancePreservation, balance_score);
        
        // All-or-nothing confidence
        let revert_score = self.calculate_revert_confidence(analysis);
        confidence.insert(SafetyProperty::AllOrNothing, revert_score);
        
        // Cross-chain consistency confidence
        if analysis.cross_chain_complexity.chain_count > 1 {
            let cross_chain_score = self.calculate_cross_chain_confidence(analysis);
            confidence.insert(SafetyProperty::CrossChainConsistency, cross_chain_score);
        }
        
        confidence
    }
    
    fn check_atomicity_violation(&self, analysis: &StructuralAnalysis) -> Option<RejectionReason> {
        // Check for operations that can't be atomic
        let has_external_dependencies = analysis.action_sequence.iter().any(|action| {
            matches!(action.action, Action::Bridge { .. }) && 
            analysis.cross_chain_complexity.bridge_count > 2
        });
        
        if has_external_dependencies && analysis.timing_risks.has_tight_deadlines {
            return Some(RejectionReason::SafetyViolation {
                property: SafetyProperty::Atomicity,
                details: "Multiple bridges with tight deadlines prevent atomic execution".to_string(),
            });
        }
        
        None
    }
    
    fn check_balance_violation(&self, analysis: &StructuralAnalysis) -> Option<RejectionReason> {
        if !analysis.balance_flows.all_flows_balanced {
            let imbalanced_tokens: Vec<String> = analysis.balance_flows.token_flows.iter()
                .filter(|(_, &flow)| flow.abs() > 10)
                .map(|(token, flow)| format!("{:?}: {}", token, flow))
                .collect();
            
            return Some(RejectionReason::SafetyViolation {
                property: SafetyProperty::BalancePreservation,
                details: format!("Token flows not balanced: {}", imbalanced_tokens.join(", ")),
            });
        }
        
        None
    }
    
    fn check_liquidity_violation(&self, analysis: &StructuralAnalysis) -> Option<RejectionReason> {
        // Check if any swap might fail due to liquidity
        for action_info in &analysis.action_sequence {
            if let Action::Swap { amount_in, token_in, .. } = &action_info.action {
                if let Some(&threshold) = self.min_liquidity_thresholds.get(token_in) {
                    if amount_in.num as u64 > threshold * 10 {
                        return Some(RejectionReason::InsufficientLiquidity {
                            required: format!("{} {:?}", amount_in.num, token_in),
                            available: format!("< {} {:?}", threshold * 10, token_in),
                        });
                    }
                }
            }
        }
        
        None
    }
    
    fn check_timing_violation(&self, analysis: &StructuralAnalysis) -> Option<RejectionReason> {
        if analysis.timing_risks.cross_chain_timing_dependency && 
           analysis.timing_risks.estimated_blocks_needed > 50 {
            return Some(RejectionReason::TimingConflict {
                details: format!(
                    "Cross-chain execution requires ~{} blocks, exceeding safe limits",
                    analysis.timing_risks.estimated_blocks_needed
                ),
            });
        }
        
        None
    }
    
    fn calculate_atomicity_confidence(&self, analysis: &StructuralAnalysis) -> f64 {
        let mut score: f64 = 1.0;
        
        // Reduce confidence for cross-chain operations
        let bridge_factor = if analysis.cross_chain_complexity.bridge_count as f64 > 2.0 { 
            2.0 
        } else { 
            analysis.cross_chain_complexity.bridge_count as f64 
        };
        score -= 0.2 * bridge_factor;
        
        // Reduce confidence for timing dependencies
        if analysis.timing_risks.cross_chain_timing_dependency {
            score -= 0.3;
        }
        
        // Boost confidence for known atomic patterns
        if analysis.pattern_type == "FlashLoanLike" {
            score += 0.2;
        }
        
        if score < 0.1 { 0.1 } else if score > 0.9 { 0.9 } else { score }
    }
    
    fn calculate_balance_confidence(&self, analysis: &StructuralAnalysis) -> f64 {
        if analysis.balance_flows.all_flows_balanced {
            0.8
        } else {
            // Calculate how unbalanced the flows are
            let max_imbalance = analysis.balance_flows.token_flows.values()
                .map(|&v| v.abs())
                .max()
                .unwrap_or(0);
            
            let imbalance_factor = max_imbalance as f64 / 1000.0;
            let confidence: f64 = 0.8 - if imbalance_factor > 0.6 { 0.6 } else { imbalance_factor };
            if confidence < 0.2 { 0.2 } else { confidence }
        }
    }
    
    fn calculate_revert_confidence(&self, analysis: &StructuralAnalysis) -> f64 {
        // Start with high confidence if all protocols are known
        let base_score = if analysis.protocol_risks.unknown_protocol_count == 0 {
            0.85
        } else {
            0.5 - (0.1 * analysis.protocol_risks.unknown_protocol_count as f64)
        };
        
        if base_score < 0.2 { 0.2 } else { base_score }
    }
    
    fn calculate_cross_chain_confidence(&self, analysis: &StructuralAnalysis) -> f64 {
        let mut score: f64 = 0.7;
        
        // Reduce for each additional chain
        let extra_chains = if analysis.cross_chain_complexity.chain_count > 2 {
            (analysis.cross_chain_complexity.chain_count - 2) as f64
        } else {
            0.0
        };
        score -= 0.15 * extra_chains;
        
        // Reduce for circular paths
        if analysis.cross_chain_complexity.has_circular_path {
            score -= 0.2;
        }
        
        if score < 0.2 { 0.2 } else { score }
    }
}

/// Extended safety checks for specific scenarios
pub struct ExtendedSafetyChecks;

impl ExtendedSafetyChecks {
    /// Check for MEV vulnerabilities
    pub fn check_mev_vulnerability(analysis: &StructuralAnalysis) -> Option<String> {
        let has_large_swaps = analysis.action_sequence.iter().any(|a| {
            matches!(&a.action, Action::Swap { amount_in, .. } if amount_in.num > 1000)
        });
        
        let has_predictable_path = analysis.action_sequence.len() > 3 && 
                                   !analysis.action_sequence.iter().any(|a| {
                                       matches!(a.action, Action::Bridge { .. })
                                   });
        
        if has_large_swaps && has_predictable_path {
            Some("Bundle may be vulnerable to MEV sandwich attacks".to_string())
        } else {
            None
        }
    }
    
    /// Check for oracle manipulation risks
    pub fn check_oracle_risks(analysis: &StructuralAnalysis) -> Option<String> {
        let uses_multiple_dexes = analysis.protocol_risks.used_protocols.len() > 2;
        let has_price_dependent_logic = analysis.action_sequence.iter().any(|a| {
            matches!(a.action, Action::Swap { .. })
        });
        
        if uses_multiple_dexes && has_price_dependent_logic {
            Some("Bundle may be vulnerable to oracle price manipulation".to_string())
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use common::types::{Rational, Chain};
    
    #[test]
    fn test_safety_violations() {
        let analysis = StructuralAnalysis {
            action_sequence: vec![],
            balance_flows: super::super::structural_analyzer::BalanceFlowAnalysis {
                token_flows: {
                    let mut flows = HashMap::new();
                    flows.insert(Token::WETH, 100);
                    flows
                },
                all_flows_balanced: false,
                unmatched_borrows: vec![(Token::WETH, 100)],
                unmatched_repays: vec![],
            },
            timing_risks: super::super::structural_analyzer::TimingRiskAnalysis {
                has_tight_deadlines: false,
                cross_chain_timing_dependency: false,
                estimated_blocks_needed: 10,
            },
            protocol_risks: super::super::structural_analyzer::ProtocolRiskAnalysis {
                used_protocols: HashSet::new(),
                unknown_protocol_count: 0,
                max_risk_score: 0.1,
            },
            cross_chain_complexity: super::super::structural_analyzer::CrossChainComplexity {
                chain_count: 1,
                bridge_count: 0,
                has_circular_path: false,
            },
            pattern_type: "Unknown".to_string(),
        };
        
        let heuristics = SafetyHeuristics::new();
        let violations = heuristics.check_safety_violations(&analysis);
        
        assert!(!violations.is_empty());
        assert!(violations.iter().any(|v| matches!(v, RejectionReason::SafetyViolation { 
            property: SafetyProperty::BalancePreservation, .. 
        })));
    }
    
    #[test]
    fn test_confidence_calculation() {
        let analysis = StructuralAnalysis {
            action_sequence: vec![],
            balance_flows: super::super::structural_analyzer::BalanceFlowAnalysis {
                token_flows: HashMap::new(),
                all_flows_balanced: true,
                unmatched_borrows: vec![],
                unmatched_repays: vec![],
            },
            timing_risks: super::super::structural_analyzer::TimingRiskAnalysis {
                has_tight_deadlines: false,
                cross_chain_timing_dependency: false,
                estimated_blocks_needed: 5,
            },
            protocol_risks: super::super::structural_analyzer::ProtocolRiskAnalysis {
                used_protocols: HashSet::new(),
                unknown_protocol_count: 0,
                max_risk_score: 0.1,
            },
            cross_chain_complexity: super::super::structural_analyzer::CrossChainComplexity {
                chain_count: 1,
                bridge_count: 0,
                has_circular_path: false,
            },
            pattern_type: "FlashLoanLike".to_string(),
        };
        
        let heuristics = SafetyHeuristics::new();
        let confidence = heuristics.calculate_property_confidence(&analysis);
        
        assert!(confidence.get(&SafetyProperty::BalancePreservation).unwrap() > &0.7);
        assert!(confidence.get(&SafetyProperty::Atomicity).unwrap() > &0.5);
    }
}