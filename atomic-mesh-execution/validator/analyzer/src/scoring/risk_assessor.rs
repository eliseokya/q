//! Risk assessment for bundles without proven patterns
//! 
//! This module provides risk-based analysis for bundles that don't match
//! any proven pattern, enabling graceful degradation with safety warnings.

use crate::common::analysis_result::{RiskProfile, RiskFactor, RiskRecommendation};
use common::types::{Bundle, Expr, Action, Protocol, Chain};
use std::collections::HashMap;

/// Risk assessor for unknown or partially matched patterns
pub struct RiskAssessor {
    /// Risk weights for different factors
    risk_weights: HashMap<String, f64>,
    /// Thresholds for risk recommendations
    risk_thresholds: RiskThresholds,
}

#[derive(Clone)]
struct RiskThresholds {
    low: f64,
    medium: f64,
    high: f64,
}

impl Default for RiskThresholds {
    fn default() -> Self {
        Self {
            low: 0.3,
            medium: 0.6,
            high: 0.8,
        }
    }
}

impl Default for RiskAssessor {
    fn default() -> Self {
        let mut weights = HashMap::new();
        weights.insert("complexity".to_string(), 0.2);
        weights.insert("cross_chain".to_string(), 0.3);
        weights.insert("unknown_action".to_string(), 0.4);
        weights.insert("gas_risk".to_string(), 0.15);
        weights.insert("timing_risk".to_string(), 0.15);
        weights.insert("protocol_risk".to_string(), 0.2);
        
        Self {
            risk_weights: weights,
            risk_thresholds: RiskThresholds::default(),
        }
    }
}

impl RiskAssessor {
    pub fn new() -> Self {
        Self::default()
    }
    
    /// Assess risk profile for a bundle
    pub fn assess_bundle_risk(&self, bundle: &Bundle) -> RiskProfile {
        let mut risk_factors = Vec::new();
        let mut total_score = 0.0;
        
        // Assess complexity risk
        let complexity = self.assess_complexity_risk(bundle);
        if complexity.1 > 0.0 {
            risk_factors.push(complexity.0);
            total_score += complexity.1 * self.get_weight("complexity");
        }
        
        // Assess cross-chain risk
        if let Some(cross_chain_risk) = self.assess_cross_chain_risk(bundle) {
            risk_factors.push(cross_chain_risk.0);
            total_score += cross_chain_risk.1 * self.get_weight("cross_chain");
        }
        
        // Assess unknown action risk
        let unknown_actions = self.find_unknown_actions(bundle);
        if !unknown_actions.is_empty() {
            risk_factors.push(RiskFactor::UnknownActions(unknown_actions));
            total_score += 0.8 * self.get_weight("unknown_action");
        }
        
        // Assess gas risk
        if let Some(gas_risk) = self.assess_gas_risk(bundle) {
            risk_factors.push(gas_risk);
            total_score += 0.6 * self.get_weight("gas_risk");
        }
        
        // Assess timing risk
        if let Some(timing_risk) = self.assess_timing_risk(bundle) {
            risk_factors.push(timing_risk);
            total_score += 0.5 * self.get_weight("timing_risk");
        }
        
        // Assess protocol risk
        let protocol_risks = self.assess_protocol_risks(bundle);
        for risk in protocol_risks {
            total_score += 0.4 * self.get_weight("protocol_risk");
            risk_factors.push(risk);
        }
        
        // Normalize score to [0, 1]
        let overall_score = total_score.min(1.0);
        
        RiskProfile {
            overall_score,
            risk_factors,
            confidence: 1.0 - overall_score, // Inverse relationship
            recommendation: self.get_recommendation(overall_score),
        }
    }
    
    /// Assess specific risks for actions without patterns
    pub fn assess_action_risk(&self, action: &Action) -> Option<RiskFactor> {
        match action {
            Action::Bridge { .. } => {
                Some(RiskFactor::CrossChainUnsafe(
                    "Bridge operation without atomicity guarantee".to_string()
                ))
            }
            Action::Swap { min_out, .. } if min_out.num == 0 => {
                Some(RiskFactor::BalanceRisk(
                    "Swap with no minimum output amount".to_string()
                ))
            }
            Action::Borrow { .. } | Action::Repay { .. } => {
                Some(RiskFactor::InvariantRisk(
                    "Flash loan without proven atomicity".to_string()
                ))
            }
            _ => None,
        }
    }
    
    /// Calculate pattern similarity for risk-based confidence
    pub fn calculate_pattern_similarity(
        &self,
        bundle: &Bundle,
        known_patterns: &[String],
    ) -> f64 {
        // Simple similarity based on action sequence matching
        let bundle_signature = self.get_bundle_signature(bundle);
        
        let max_similarity = known_patterns.iter()
            .map(|pattern| self.string_similarity(&bundle_signature, pattern))
            .max_by(|a, b| a.partial_cmp(b).unwrap())
            .unwrap_or(0.0);
        
        max_similarity
    }
    
    // Risk assessment helpers
    
    fn assess_complexity_risk(&self, bundle: &Bundle) -> (RiskFactor, f64) {
        let action_count = self.count_actions(&bundle.expr);
        let score = match action_count {
            0..=3 => 0.1,
            4..=6 => 0.3,
            7..=10 => 0.6,
            _ => 0.9,
        };
        
        (RiskFactor::HighComplexity(score), score)
    }
    
    fn assess_cross_chain_risk(&self, bundle: &Bundle) -> Option<(RiskFactor, f64)> {
        let chains = self.extract_chains(&bundle.expr);
        if chains.len() > 1 {
            let risk_msg = format!("Cross-chain operation across {} chains", chains.len());
            let score = 0.3 + (chains.len() as f64 * 0.2).min(0.7);
            Some((RiskFactor::CrossChainUnsafe(risk_msg), score))
        } else {
            None
        }
    }
    
    fn find_unknown_actions(&self, bundle: &Bundle) -> Vec<String> {
        let mut unknown = Vec::new();
        self.check_unknown_actions(&bundle.expr, &mut unknown);
        unknown
    }
    
    fn check_unknown_actions(&self, expr: &Expr, unknown: &mut Vec<String>) {
        match expr {
            Expr::Action { action } => {
                if self.is_unknown_action(action) {
                    unknown.push(format!("{:?}", action));
                }
            }
            Expr::Seq { first, second } => {
                self.check_unknown_actions(first, unknown);
                self.check_unknown_actions(second, unknown);
            }
            Expr::Parallel { exprs } => {
                for e in exprs {
                    self.check_unknown_actions(e, unknown);
                }
            }
            Expr::OnChain { expr, .. } => {
                self.check_unknown_actions(expr, unknown);
            }
        }
    }
    
    fn is_unknown_action(&self, action: &Action) -> bool {
        // Check if action uses unknown protocols or has unusual parameters
        match action {
            Action::Swap { protocol, .. } => !self.is_known_protocol(protocol),
            Action::Borrow { protocol, .. } => !self.is_known_protocol(protocol),
            Action::Repay { protocol, .. } => !self.is_known_protocol(protocol),
            _ => false,
        }
    }
    
    fn is_known_protocol(&self, protocol: &Protocol) -> bool {
        matches!(
            protocol,
            Protocol::UniswapV2 | Protocol::Aave | Protocol::Compound
        )
    }
    
    fn assess_gas_risk(&self, bundle: &Bundle) -> Option<RiskFactor> {
        for constraint in &bundle.constraints {
            if let common::types::Constraint::MaxGas { amount } = constraint {
                if *amount < 300_000 {
                    return Some(RiskFactor::GasRisk(
                        "Very low gas limit may cause execution failure".to_string()
                    ));
                } else if *amount > 5_000_000 {
                    return Some(RiskFactor::GasRisk(
                        "Extremely high gas consumption".to_string()
                    ));
                }
            }
        }
        None
    }
    
    fn assess_timing_risk(&self, bundle: &Bundle) -> Option<RiskFactor> {
        for constraint in &bundle.constraints {
            if let common::types::Constraint::Deadline { blocks } = constraint {
                if *blocks < 5 {
                    return Some(RiskFactor::TimingRisk(
                        "Very tight deadline may not be achievable".to_string()
                    ));
                }
            }
        }
        None
    }
    
    fn assess_protocol_risks(&self, bundle: &Bundle) -> Vec<RiskFactor> {
        let mut risks = Vec::new();
        let protocols = self.extract_protocols(&bundle.expr);
        
        // Check for risky protocol combinations
        if protocols.len() > 3 {
            risks.push(RiskFactor::InvariantRisk(
                "Too many protocols in one bundle increases complexity".to_string()
            ));
        }
        
        risks
    }
    
    fn get_weight(&self, factor: &str) -> f64 {
        self.risk_weights.get(factor).copied().unwrap_or(0.1)
    }
    
    fn get_recommendation(&self, score: f64) -> RiskRecommendation {
        if score < self.risk_thresholds.low {
            RiskRecommendation::LowRisk
        } else if score < self.risk_thresholds.medium {
            RiskRecommendation::MediumRisk
        } else if score < self.risk_thresholds.high {
            RiskRecommendation::HighRisk
        } else {
            RiskRecommendation::UnacceptableRisk
        }
    }
    
    fn count_actions(&self, expr: &Expr) -> usize {
        match expr {
            Expr::Action { .. } => 1,
            Expr::Seq { first, second } => {
                self.count_actions(first) + self.count_actions(second)
            }
            Expr::Parallel { exprs } => {
                exprs.iter().map(|e| self.count_actions(e)).sum()
            }
            Expr::OnChain { expr, .. } => self.count_actions(expr),
        }
    }
    
    fn extract_chains(&self, expr: &Expr) -> Vec<Chain> {
        use std::collections::HashSet;
        let mut chains = HashSet::new();
        self.collect_chains(expr, &mut chains);
        let mut chains_vec: Vec<Chain> = chains.into_iter().collect();
        chains_vec.sort_by(|a, b| format!("{:?}", a).cmp(&format!("{:?}", b)));
        chains_vec
    }
    
    fn collect_chains(&self, expr: &Expr, chains: &mut std::collections::HashSet<Chain>) {
        match expr {
            Expr::Action { action } => {
                if let Action::Bridge { chain, .. } = action {
                    chains.insert(chain.clone());
                }
            }
            Expr::OnChain { chain, expr } => {
                chains.insert(chain.clone());
                self.collect_chains(expr, chains);
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
        }
    }
    
    fn extract_protocols(&self, expr: &Expr) -> Vec<Protocol> {
        use std::collections::HashSet;
        let mut protocols = HashSet::new();
        self.collect_protocols(expr, &mut protocols);
        let mut protocols_vec: Vec<Protocol> = protocols.into_iter().collect();
        protocols_vec.sort_by(|a, b| format!("{:?}", a).cmp(&format!("{:?}", b)));
        protocols_vec
    }
    
    fn collect_protocols(&self, expr: &Expr, protocols: &mut std::collections::HashSet<Protocol>) {
        match expr {
            Expr::Action { action } => {
                match action {
                    Action::Swap { protocol, .. } |
                    Action::Borrow { protocol, .. } |
                    Action::Repay { protocol, .. } |
                    Action::Deposit { protocol, .. } |
                    Action::Withdraw { protocol, .. } => {
                        protocols.insert(protocol.clone());
                    }
                    _ => {}
                }
            }
            Expr::Seq { first, second } => {
                self.collect_protocols(first, protocols);
                self.collect_protocols(second, protocols);
            }
            Expr::Parallel { exprs } => {
                for e in exprs {
                    self.collect_protocols(e, protocols);
                }
            }
            Expr::OnChain { expr, .. } => {
                self.collect_protocols(expr, protocols);
            }
        }
    }
    
    fn get_bundle_signature(&self, bundle: &Bundle) -> String {
        // Create a simplified string representation of the bundle structure
        self.expr_to_signature(&bundle.expr)
    }
    
    fn expr_to_signature(&self, expr: &Expr) -> String {
        match expr {
            Expr::Action { action } => self.action_to_signature(action),
            Expr::Seq { first, second } => {
                format!("seq({},{})", 
                    self.expr_to_signature(first),
                    self.expr_to_signature(second))
            }
            Expr::Parallel { exprs } => {
                let sigs: Vec<String> = exprs.iter()
                    .map(|e| self.expr_to_signature(e))
                    .collect();
                format!("parallel({})", sigs.join(","))
            }
            Expr::OnChain { chain, expr } => {
                format!("onchain({:?},{})", chain, self.expr_to_signature(expr))
            }
        }
    }
    
    fn action_to_signature(&self, action: &Action) -> String {
        match action {
            Action::Swap { .. } => "swap".to_string(),
            Action::Borrow { .. } => "borrow".to_string(),
            Action::Repay { .. } => "repay".to_string(),
            Action::Bridge { .. } => "bridge".to_string(),
            Action::Deposit { .. } => "deposit".to_string(),
            Action::Withdraw { .. } => "withdraw".to_string(),
        }
    }
    
    fn string_similarity(&self, s1: &str, s2: &str) -> f64 {
        // Simple character-based similarity
        let matches = s1.chars().zip(s2.chars()).filter(|(a, b)| a == b).count();
        let max_len = s1.len().max(s2.len());
        if max_len == 0 {
            1.0
        } else {
            matches as f64 / max_len as f64
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_risk_assessor_creation() {
        let assessor = RiskAssessor::new();
        assert!(assessor.risk_weights.contains_key("complexity"));
    }
    
    #[test]
    fn test_risk_recommendation_thresholds() {
        let assessor = RiskAssessor::new();
        
        assert_eq!(assessor.get_recommendation(0.2), RiskRecommendation::LowRisk);
        assert_eq!(assessor.get_recommendation(0.5), RiskRecommendation::MediumRisk);
        assert_eq!(assessor.get_recommendation(0.7), RiskRecommendation::HighRisk);
        assert_eq!(assessor.get_recommendation(0.9), RiskRecommendation::UnacceptableRisk);
    }
}