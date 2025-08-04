//! Structural heuristic analyzer for patterns without formal proofs
//! 
//! This module implements heuristic analysis techniques to assess
//! bundle safety when mathematical proofs are not available.

use common::types::{Bundle, Expr, Action, Token, Protocol, Chain};
use crate::fallback::{SafetyAnalysis, RiskLevel, RiskAssessment};
use crate::common::pattern_types::SafetyProperty;
use std::collections::{HashMap, HashSet};
use num_traits::sign::Signed;

/// Structural analyzer for heuristic safety assessment
pub struct StructuralAnalyzer {
    known_safe_protocols: HashSet<Protocol>,
    known_safe_tokens: HashSet<Token>,
    protocol_risk_scores: HashMap<Protocol, f64>,
}

impl StructuralAnalyzer {
    pub fn new() -> Self {
        let mut known_safe_protocols = HashSet::new();
        known_safe_protocols.insert(Protocol::Aave);
        known_safe_protocols.insert(Protocol::UniswapV2);
        known_safe_protocols.insert(Protocol::Compound);
        
        let mut known_safe_tokens = HashSet::new();
        known_safe_tokens.insert(Token::WETH);
        known_safe_tokens.insert(Token::USDC);
        known_safe_tokens.insert(Token::DAI);
        
        let mut protocol_risk_scores = HashMap::new();
        protocol_risk_scores.insert(Protocol::Aave, 0.1);
        protocol_risk_scores.insert(Protocol::UniswapV2, 0.15);
        protocol_risk_scores.insert(Protocol::Compound, 0.12);
        
        Self {
            known_safe_protocols,
            known_safe_tokens,
            protocol_risk_scores,
        }
    }
    
    /// Perform comprehensive structural analysis
    pub fn analyze_structure(&self, bundle: &Bundle) -> StructuralAnalysis {
        let action_sequence = self.extract_action_sequence(&bundle.expr);
        let balance_flows = self.analyze_balance_flows(&action_sequence);
        let timing_risks = self.analyze_timing_risks(&action_sequence);
        let protocol_risks = self.analyze_protocol_risks(&action_sequence);
        let cross_chain_complexity = self.analyze_cross_chain_complexity(&action_sequence);
        let pattern_type = self.detect_pattern_type(&action_sequence);
        
        StructuralAnalysis {
            action_sequence,
            balance_flows,
            timing_risks,
            protocol_risks,
            cross_chain_complexity,
            pattern_type,
        }
    }
    
    /// Generate safety analysis from structural analysis
    pub fn generate_safety_analysis(&self, analysis: &StructuralAnalysis) -> SafetyAnalysis {
        let mut confidence_per_property = HashMap::new();
        
        // Analyze balance preservation
        let balance_preserved = self.check_balance_preservation(&analysis.balance_flows);
        confidence_per_property.insert(
            SafetyProperty::BalancePreservation,
            if balance_preserved.unwrap_or(false) { 0.7 } else { 0.3 }
        );
        
        // Analyze atomicity likelihood
        let atomicity_likely = self.check_atomicity_likelihood(analysis);
        confidence_per_property.insert(
            SafetyProperty::Atomicity,
            if atomicity_likely.unwrap_or(false) { 0.6 } else { 0.2 }
        );
        
        // Analyze revert safety
        let revert_safe = self.check_revert_safety(analysis);
        confidence_per_property.insert(
            SafetyProperty::AllOrNothing,
            if revert_safe.unwrap_or(false) { 0.8 } else { 0.4 }
        );
        
        // Calculate value extraction risk
        let value_extraction_risk = self.calculate_value_extraction_risk(analysis);
        
        SafetyAnalysis {
            balance_preserved,
            atomicity_likely,
            revert_safe,
            value_extraction_risk: Some(value_extraction_risk),
            confidence_per_property,
        }
    }
    
    /// Generate risk assessment from structural analysis
    pub fn generate_risk_assessment(&self, analysis: &StructuralAnalysis) -> RiskAssessment {
        let mut risk_factors = HashMap::new();
        let mut overall_score = 0.0;
        
        // Protocol risks
        if analysis.protocol_risks.unknown_protocol_count > 0 {
            let risk = 0.3 * analysis.protocol_risks.unknown_protocol_count as f64;
            risk_factors.insert("unknown_protocols".to_string(), risk);
            overall_score += risk;
        }
        
        // Timing risks
        if analysis.timing_risks.has_tight_deadlines {
            risk_factors.insert("timing_pressure".to_string(), 0.25);
            overall_score += 0.25;
        }
        
        // Cross-chain risks
        if analysis.cross_chain_complexity.chain_count > 1 {
            let risk = 0.2 * (analysis.cross_chain_complexity.chain_count - 1) as f64;
            risk_factors.insert("cross_chain_complexity".to_string(), risk);
            overall_score += risk;
        }
        
        // Balance flow risks
        if !analysis.balance_flows.all_flows_balanced {
            risk_factors.insert("unbalanced_flows".to_string(), 0.4);
            overall_score += 0.4;
        }
        
        let overall_risk = match overall_score {
            s if s < 0.3 => RiskLevel::Low,
            s if s < 0.6 => RiskLevel::Medium,
            s if s < 0.8 => RiskLevel::High,
            _ => RiskLevel::Critical,
        };
        
        let mitigation_strategies = self.generate_mitigation_strategies(&risk_factors);
        
        RiskAssessment {
            overall_risk,
            risk_factors,
            mitigation_strategies,
            confidence_in_assessment: 0.6 + (0.2 * analysis.action_sequence.len().min(5) as f64 / 5.0),
        }
    }
    
    fn extract_action_sequence(&self, expr: &Expr) -> Vec<ActionInfo> {
        let mut actions = Vec::new();
        self.extract_actions_recursive(expr, &mut actions, Chain::Polygon); // Default chain
        actions
    }
    
    fn extract_actions_recursive(&self, expr: &Expr, actions: &mut Vec<ActionInfo>, current_chain: Chain) {
        match expr {
            Expr::Action { action } => {
                actions.push(ActionInfo {
                    action: action.clone(),
                    chain: current_chain,
                    position: actions.len(),
                });
            }
            Expr::Seq { first, second } => {
                self.extract_actions_recursive(first, actions, current_chain.clone());
                self.extract_actions_recursive(second, actions, current_chain);
            }
            Expr::Parallel { exprs } => {
                for e in exprs {
                    self.extract_actions_recursive(e, actions, current_chain.clone());
                }
            }
            Expr::OnChain { chain, expr } => {
                self.extract_actions_recursive(expr, actions, chain.clone());
            }
        }
    }
    
    fn analyze_balance_flows(&self, actions: &[ActionInfo]) -> BalanceFlowAnalysis {
        let mut token_flows: HashMap<Token, i64> = HashMap::new();
        let mut unmatched_borrows = Vec::new();
        let mut unmatched_repays = Vec::new();
        
        for action_info in actions {
            match &action_info.action {
                Action::Borrow { amount, token, .. } => {
                    *token_flows.entry(token.clone()).or_insert(0) += amount.num as i64;
                    unmatched_borrows.push((token.clone(), amount.num as i64));
                }
                Action::Repay { amount, token, .. } => {
                    *token_flows.entry(token.clone()).or_insert(0) -= amount.num as i64;
                    if let Some(pos) = unmatched_borrows.iter().position(|(t, _)| t == token) {
                        unmatched_borrows.remove(pos);
                    } else {
                        unmatched_repays.push((token.clone(), amount.num as i64));
                    }
                }
                Action::Swap { amount_in, token_in, token_out, min_out, .. } => {
                    *token_flows.entry(token_in.clone()).or_insert(0) -= amount_in.num as i64;
                    *token_flows.entry(token_out.clone()).or_insert(0) += min_out.num as i64;
                }
                Action::Bridge { .. } => {
                    // Bridges are neutral for balance analysis
                }
                Action::Deposit { .. } => {
                    // Deposits are tracked separately
                }
                Action::Withdraw { .. } => {
                    // Withdrawals are tracked separately
                }
            }
        }
        
        let all_flows_balanced = token_flows.values().all(|&flow| flow.abs() < 10);
        
        BalanceFlowAnalysis {
            token_flows,
            all_flows_balanced,
            unmatched_borrows,
            unmatched_repays,
        }
    }
    
    fn analyze_timing_risks(&self, actions: &[ActionInfo]) -> TimingRiskAnalysis {
        let has_cross_chain = actions.windows(2).any(|w| w[0].chain != w[1].chain);
        let action_count = actions.len();
        
        TimingRiskAnalysis {
            has_tight_deadlines: action_count > 10,
            cross_chain_timing_dependency: has_cross_chain,
            estimated_blocks_needed: action_count as u32 * 2,
        }
    }
    
    fn analyze_protocol_risks(&self, actions: &[ActionInfo]) -> ProtocolRiskAnalysis {
        let mut used_protocols = HashSet::new();
        let mut unknown_protocol_count = 0;
        let mut max_risk_score: f64 = 0.0;
        
        for action_info in actions {
            if let Some(protocol) = get_action_protocol(&action_info.action) {
                used_protocols.insert(protocol.clone());
                
                if !self.known_safe_protocols.contains(&protocol) {
                    unknown_protocol_count += 1;
                }
                
                if let Some(&risk) = self.protocol_risk_scores.get(&protocol) {
                    if risk > max_risk_score {
                        max_risk_score = risk;
                    }
                } else {
                    if 0.5 > max_risk_score {
                        max_risk_score = 0.5; // Unknown protocol default risk
                    }
                }
            }
        }
        
        ProtocolRiskAnalysis {
            used_protocols,
            unknown_protocol_count,
            max_risk_score,
        }
    }
    
    fn analyze_cross_chain_complexity(&self, actions: &[ActionInfo]) -> CrossChainComplexity {
        let mut used_chains = HashSet::new();
        let mut bridge_count = 0;
        
        for action_info in actions {
            used_chains.insert(action_info.chain.clone());
            if matches!(action_info.action, Action::Bridge { .. }) {
                bridge_count += 1;
            }
        }
        
        CrossChainComplexity {
            chain_count: used_chains.len(),
            bridge_count,
            has_circular_path: self.has_circular_chain_path(actions),
        }
    }
    
    fn detect_pattern_type(&self, actions: &[ActionInfo]) -> String {
        // Simple pattern detection heuristics
        if actions.len() >= 2 {
            let first_is_borrow = matches!(actions.first().unwrap().action, Action::Borrow { .. });
            let last_is_repay = matches!(actions.last().unwrap().action, Action::Repay { .. });
            
            if first_is_borrow && last_is_repay {
                return "FlashLoanLike".to_string();
            }
        }
        
        let swap_count = actions.iter().filter(|a| matches!(a.action, Action::Swap { .. })).count();
        if swap_count >= 3 {
            return "Arbitrage".to_string();
        }
        
        if actions.iter().any(|a| matches!(a.action, Action::Bridge { .. })) {
            return "CrossChain".to_string();
        }
        
        "Unknown".to_string()
    }
    
    fn check_balance_preservation(&self, flows: &BalanceFlowAnalysis) -> Option<bool> {
        Some(flows.all_flows_balanced && flows.unmatched_borrows.is_empty())
    }
    
    fn check_atomicity_likelihood(&self, analysis: &StructuralAnalysis) -> Option<bool> {
        // Heuristic: flash loan-like patterns are likely atomic
        let is_flash_loan_like = analysis.pattern_type == "FlashLoanLike";
        let has_unmatched_operations = !analysis.balance_flows.unmatched_borrows.is_empty() ||
                                       !analysis.balance_flows.unmatched_repays.is_empty();
        
        Some(is_flash_loan_like && !has_unmatched_operations)
    }
    
    fn check_revert_safety(&self, analysis: &StructuralAnalysis) -> Option<bool> {
        // All known protocols support revert
        let all_protocols_safe = analysis.protocol_risks.unknown_protocol_count == 0;
        Some(all_protocols_safe)
    }
    
    fn calculate_value_extraction_risk(&self, analysis: &StructuralAnalysis) -> f64 {
        let mut risk = 0.0;
        
        // Unknown protocols increase risk
        risk += 0.1 * analysis.protocol_risks.unknown_protocol_count as f64;
        
        // Unbalanced flows increase risk
        if !analysis.balance_flows.all_flows_balanced {
            risk += 0.3;
        }
        
        // Cross-chain complexity increases risk
        risk += 0.1 * ((analysis.cross_chain_complexity.chain_count as i32 - 1).max(0) as f64);
        
        if risk > 1.0 { 1.0 } else { risk }
    }
    
    fn has_circular_chain_path(&self, actions: &[ActionInfo]) -> bool {
        if actions.len() < 3 {
            return false;
        }
        
        let first_chain = actions.first().unwrap().chain.clone();
        let mut visited_other_chain = false;
        
        for action in actions.iter().skip(1) {
            if action.chain.clone() != first_chain {
                visited_other_chain = true;
            } else if visited_other_chain {
                return true; // Returned to first chain
            }
        }
        
        false
    }
    
    fn generate_mitigation_strategies(&self, risk_factors: &HashMap<String, f64>) -> Vec<String> {
        let mut strategies = Vec::new();
        
        if risk_factors.contains_key("unknown_protocols") {
            strategies.push("Verify protocol contracts before execution".to_string());
            strategies.push("Use conservative slippage parameters".to_string());
        }
        
        if risk_factors.contains_key("timing_pressure") {
            strategies.push("Increase deadline buffers".to_string());
            strategies.push("Monitor gas prices for optimal execution".to_string());
        }
        
        if risk_factors.contains_key("cross_chain_complexity") {
            strategies.push("Implement bridge failure recovery".to_string());
            strategies.push("Use atomic bridge protocols when available".to_string());
        }
        
        if risk_factors.contains_key("unbalanced_flows") {
            strategies.push("Add balance verification checks".to_string());
            strategies.push("Implement emergency withdrawal mechanisms".to_string());
        }
        
        strategies
    }
}

/// Detailed structural analysis results
#[derive(Debug)]
pub struct StructuralAnalysis {
    pub action_sequence: Vec<ActionInfo>,
    pub balance_flows: BalanceFlowAnalysis,
    pub timing_risks: TimingRiskAnalysis,
    pub protocol_risks: ProtocolRiskAnalysis,
    pub cross_chain_complexity: CrossChainComplexity,
    pub pattern_type: String,
}

#[derive(Debug, Clone)]
pub struct ActionInfo {
    pub action: Action,
    pub chain: Chain,
    pub position: usize,
}

#[derive(Debug)]
pub struct BalanceFlowAnalysis {
    pub token_flows: HashMap<Token, i64>,
    pub all_flows_balanced: bool,
    pub unmatched_borrows: Vec<(Token, i64)>,
    pub unmatched_repays: Vec<(Token, i64)>,
}

#[derive(Debug)]
pub struct TimingRiskAnalysis {
    pub has_tight_deadlines: bool,
    pub cross_chain_timing_dependency: bool,
    pub estimated_blocks_needed: u32,
}

#[derive(Debug)]
pub struct ProtocolRiskAnalysis {
    pub used_protocols: HashSet<Protocol>,
    pub unknown_protocol_count: usize,
    pub max_risk_score: f64,
}

#[derive(Debug)]
pub struct CrossChainComplexity {
    pub chain_count: usize,
    pub bridge_count: usize,
    pub has_circular_path: bool,
}

// Helper function to extract protocol from action
fn get_action_protocol(action: &Action) -> Option<Protocol> {
    match action {
        Action::Borrow { protocol, .. } |
        Action::Repay { protocol, .. } |
        Action::Swap { protocol, .. } => Some(protocol.clone()),
        Action::Deposit { .. } |
        Action::Withdraw { .. } |
        Action::Bridge { .. } => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use common::types::{Rational, Constraint};
    
    #[test]
    fn test_flash_loan_pattern_detection() {
        let bundle = Bundle {
            name: "test".to_string(),
            start_chain: Chain::Polygon,
            expr: Expr::Seq {
                first: Box::new(Expr::Action {
                    action: Action::Borrow {
                        amount: Rational::from_integer(100),
                        token: Token::WETH,
                        protocol: Protocol::Aave,
                    }
                }),
                second: Box::new(Expr::Action {
                    action: Action::Repay {
                        amount: Rational::from_integer(100),
                        token: Token::WETH,
                        protocol: Protocol::Aave,
                    }
                }),
            },
            constraints: vec![],
        };
        
        let analyzer = StructuralAnalyzer::new();
        let analysis = analyzer.analyze_structure(&bundle);
        
        assert_eq!(analysis.pattern_type, "FlashLoanLike");
        assert!(analysis.balance_flows.all_flows_balanced);
    }
    
    #[test]
    fn test_risk_assessment() {
        let analyzer = StructuralAnalyzer::new();
        let mut analysis = StructuralAnalysis {
            action_sequence: vec![],
            balance_flows: BalanceFlowAnalysis {
                token_flows: HashMap::new(),
                all_flows_balanced: false,
                unmatched_borrows: vec![(Token::WETH, 100)],
                unmatched_repays: vec![],
            },
            timing_risks: TimingRiskAnalysis {
                has_tight_deadlines: false,
                cross_chain_timing_dependency: false,
                estimated_blocks_needed: 5,
            },
            protocol_risks: ProtocolRiskAnalysis {
                used_protocols: HashSet::new(),
                unknown_protocol_count: 1,
                max_risk_score: 0.5,
            },
            cross_chain_complexity: CrossChainComplexity {
                chain_count: 2,
                bridge_count: 1,
                has_circular_path: false,
            },
            pattern_type: "Unknown".to_string(),
        };
        
        let risk = analyzer.generate_risk_assessment(&analysis);
        assert!(matches!(risk.overall_risk, RiskLevel::High | RiskLevel::Critical));
        assert!(risk.risk_factors.contains_key("unbalanced_flows"));
    }
}