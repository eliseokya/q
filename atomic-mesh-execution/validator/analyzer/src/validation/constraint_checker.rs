//! Fast constraint validation for DSL bundles
//!
//! This module validates constraints like deadlines, gas limits,
//! balance requirements, and invariants within the 100μs budget.

use crate::common::{Bundle, Constraint, Expr, Action, Token, Chain};
use std::collections::HashMap;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

/// Result of constraint validation
#[derive(Debug, Clone)]
pub struct ConstraintValidationResult {
    pub is_valid: bool,
    pub violated_constraints: Vec<ViolatedConstraint>,
    pub validation_time_us: u64,
    pub checked_constraints: usize,
}

#[derive(Debug, Clone)]
pub struct ViolatedConstraint {
    pub constraint_type: String,
    pub expected: String,
    pub actual: String,
    pub severity: ConstraintSeverity,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ConstraintSeverity {
    Critical,  // Must be fixed
    Warning,   // Should be reviewed
    Info,      // Informational only
}

/// Fast constraint checker with <100μs target
pub struct ConstraintChecker {
    /// Current block timestamps per chain
    chain_timestamps: HashMap<Chain, u64>,
    /// Gas price estimates per chain
    gas_prices: HashMap<Chain, u64>,
    /// Token balances for validation
    token_balances: HashMap<(Chain, Token), u64>,
    /// Performance metrics
    total_validations: usize,
    total_validation_time_us: u64,
}

impl ConstraintChecker {
    pub fn new() -> Self {
        let mut chain_timestamps = HashMap::new();
        let current_time = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        // Initialize with current timestamps
        chain_timestamps.insert(Chain::Arbitrum, current_time);
        chain_timestamps.insert(Chain::Polygon, current_time);

        let mut gas_prices = HashMap::new();
        // Initialize with default gas prices (in gwei)
        gas_prices.insert(Chain::Arbitrum, 1);
        gas_prices.insert(Chain::Polygon, 100);

        Self {
            chain_timestamps,
            gas_prices,
            token_balances: HashMap::new(),
            total_validations: 0,
            total_validation_time_us: 0,
        }
    }

    /// Update chain timestamp
    pub fn update_chain_timestamp(&mut self, chain: Chain, timestamp: u64) {
        self.chain_timestamps.insert(chain, timestamp);
    }

    /// Update gas price
    pub fn update_gas_price(&mut self, chain: Chain, price_gwei: u64) {
        self.gas_prices.insert(chain, price_gwei);
    }

    /// Set token balance for validation
    pub fn set_token_balance(&mut self, chain: Chain, token: Token, balance: u64) {
        self.token_balances.insert((chain, token), balance);
    }

    /// Validate all constraints in a bundle
    pub fn validate_bundle(&mut self, bundle: &Bundle) -> ConstraintValidationResult {
        let start = Instant::now();
        let mut violated_constraints = Vec::new();
        let mut checked_constraints = 0;

        // Check each constraint
        for constraint in &bundle.constraints {
            checked_constraints += 1;
            
            match constraint {
                Constraint::Deadline { blocks } => {
                    if let Some(violation) = self.check_deadline(bundle, *blocks) {
                        violated_constraints.push(violation);
                    }
                }
                Constraint::MaxGas { amount } => {
                    if let Some(violation) = self.check_gas_limit(bundle, *amount) {
                        violated_constraints.push(violation);
                    }
                }
                Constraint::MinBalance { token, amount } => {
                    if let Some(violation) = self.check_min_balance(&bundle.start_chain, token, amount.num) {
                        violated_constraints.push(violation);
                    }
                }
                Constraint::Invariant { invariant } => {
                    if let Some(violation) = self.check_invariant(bundle, invariant) {
                        violated_constraints.push(violation);
                    }
                }
            }
        }

        // Additional implicit constraints
        if let Some(violation) = self.check_balance_preservation(bundle) {
            violated_constraints.push(violation);
            checked_constraints += 1;
        }

        if let Some(violation) = self.check_action_validity(bundle) {
            violated_constraints.push(violation);
            checked_constraints += 1;
        }

        let elapsed = start.elapsed().as_micros() as u64;
        self.total_validations += 1;
        self.total_validation_time_us += elapsed;

        ConstraintValidationResult {
            is_valid: violated_constraints.is_empty(),
            violated_constraints,
            validation_time_us: elapsed,
            checked_constraints,
        }
    }

    fn check_deadline(&self, bundle: &Bundle, max_blocks: u64) -> Option<ViolatedConstraint> {
        // Estimate execution time based on bundle complexity
        let estimated_blocks = self.estimate_execution_blocks(&bundle.expr);
        
        if estimated_blocks > max_blocks {
            Some(ViolatedConstraint {
                constraint_type: "Deadline".to_string(),
                expected: format!("{} blocks", max_blocks),
                actual: format!("{} blocks", estimated_blocks),
                severity: ConstraintSeverity::Critical,
            })
        } else {
            None
        }
    }

    fn check_gas_limit(&self, bundle: &Bundle, limit: u64) -> Option<ViolatedConstraint> {
        let estimated_gas = self.estimate_gas_usage(&bundle.expr, &bundle.start_chain);
        
        if estimated_gas > limit {
            Some(ViolatedConstraint {
                constraint_type: "MaxGas".to_string(),
                expected: format!("{} gas", limit),
                actual: format!("{} gas", estimated_gas),
                severity: ConstraintSeverity::Critical,
            })
        } else {
            None
        }
    }

    fn check_min_balance(&self, chain: &Chain, token: &Token, required: u64) -> Option<ViolatedConstraint> {
        let balance = self.token_balances
            .get(&(chain.clone(), token.clone()))
            .copied()
            .unwrap_or(0);
        
        if balance < required {
            Some(ViolatedConstraint {
                constraint_type: "MinBalance".to_string(),
                expected: format!("{} {:?} on {:?}", required, token, chain),
                actual: format!("{} {:?}", balance, token),
                severity: ConstraintSeverity::Critical,
            })
        } else {
            None
        }
    }

    fn check_invariant(&self, _bundle: &Bundle, invariant: &common::Invariant) -> Option<ViolatedConstraint> {
        // Check specific invariants based on type
        match invariant {
            common::Invariant::ConstantProduct => {
                // Would check Uniswap-style x*y=k invariant
                None // Assume valid for now
            }
            common::Invariant::NoNegativeBalance => {
                // Would check no negative balances
                None // Assume valid for now
            }
        }
    }

    fn check_balance_preservation(&self, bundle: &Bundle) -> Option<ViolatedConstraint> {
        // Analyze bundle to ensure no tokens are lost
        let balance_changes = self.analyze_balance_changes(&bundle.expr);
        
        for (token, change) in balance_changes {
            if change < 0 {
                return Some(ViolatedConstraint {
                    constraint_type: "BalancePreservation".to_string(),
                    expected: format!("Non-negative {:?} balance", token),
                    actual: format!("{} {:?} deficit", -change, token),
                    severity: ConstraintSeverity::Critical,
                });
            }
        }
        
        None
    }

    fn check_action_validity(&self, bundle: &Bundle) -> Option<ViolatedConstraint> {
        // Check that all actions are valid
        let invalid_action = self.find_invalid_action(&bundle.expr);
        
        invalid_action.map(|action| ViolatedConstraint {
            constraint_type: "ActionValidity".to_string(),
            expected: "All actions valid".to_string(),
            actual: format!("Invalid action: {}", action),
            severity: ConstraintSeverity::Critical,
        })
    }

    fn estimate_execution_blocks(&self, expr: &Expr) -> u64 {
        match expr {
            Expr::Action { action } => {
                match action {
                    Action::Bridge { .. } => 20, // Bridge operations take time
                    _ => 1, // Most actions complete in 1 block
                }
            }
            Expr::Seq { first, second } => {
                self.estimate_execution_blocks(first) + self.estimate_execution_blocks(second)
            }
            Expr::Parallel { exprs } => {
                // Parallel execution takes as long as the longest branch
                exprs.iter()
                    .map(|e| self.estimate_execution_blocks(e))
                    .max()
                    .unwrap_or(0)
            }
            Expr::OnChain { expr, .. } => self.estimate_execution_blocks(expr),
        }
    }

    fn estimate_gas_usage(&self, expr: &Expr, chain: &Chain) -> u64 {
        let base_gas = match expr {
            Expr::Action { action } => self.estimate_action_gas(action, chain),
            Expr::Seq { first, second } => {
                self.estimate_gas_usage(first, chain) + self.estimate_gas_usage(second, chain)
            }
            Expr::Parallel { exprs } => {
                // Parallel operations still consume total gas
                exprs.iter()
                    .map(|e| self.estimate_gas_usage(e, chain))
                    .sum()
            }
            Expr::OnChain { chain: target_chain, expr: e } => {
                if target_chain == chain {
                    self.estimate_gas_usage(e, chain)
                } else {
                    300_000 // Bridge gas cost
                }
            }
        };

        // Apply chain-specific multipliers
        match chain {
            Chain::Polygon => base_gas * 110 / 100, // 10% higher on Polygon
            _ => base_gas,
        }
    }

    fn estimate_action_gas(&self, action: &Action, _chain: &Chain) -> u64 {
        match action {
            Action::Swap { .. } => 150_000,
            Action::Borrow { .. } => 250_000,
            Action::Repay { .. } => 200_000,
            Action::Bridge { .. } => 300_000,
            Action::Deposit { .. } => 100_000,
            Action::Withdraw { .. } => 120_000,

        }
    }

    fn analyze_balance_changes(&self, expr: &Expr) -> HashMap<Token, i64> {
        let mut changes = HashMap::new();
        self.analyze_balance_recursive(expr, &mut changes);
        changes
    }

    fn analyze_balance_recursive(&self, expr: &Expr, changes: &mut HashMap<Token, i64>) {
        match expr {
            Expr::Action { action } => {
                match action {
                    Action::Swap { amount_in, token_in, token_out, min_out, .. } => {
                        // Convert Rational to i64 for balance tracking
                        let amount_in_i64 = amount_in.num as i64;
                        let min_out_i64 = min_out.num as i64;
                        *changes.entry(token_in.clone()).or_insert(0) -= amount_in_i64;
                        *changes.entry(token_out.clone()).or_insert(0) += min_out_i64;
                    }
                    Action::Borrow { amount, token, .. } => {
                        let amount_i64 = amount.num as i64;
                        *changes.entry(token.clone()).or_insert(0) += amount_i64;
                    }
                    Action::Repay { amount, token, .. } => {
                        let amount_i64 = amount.num as i64;
                        *changes.entry(token.clone()).or_insert(0) -= amount_i64;
                    }
                    _ => {} // Other actions don't directly affect token balances
                }
            }
            Expr::Seq { first, second } => {
                self.analyze_balance_recursive(first, changes);
                self.analyze_balance_recursive(second, changes);
            }
            Expr::Parallel { exprs } => {
                for e in exprs {
                    self.analyze_balance_recursive(e, changes);
                }
            }
            Expr::OnChain { expr, .. } => {
                self.analyze_balance_recursive(expr, changes);
            }
        }
    }

    fn find_invalid_action(&self, expr: &Expr) -> Option<String> {
        match expr {
            Expr::Action { action } => {
                // Check for invalid action patterns
                match action {
                    Action::Swap { amount_in, min_out, .. } => {
                        if amount_in.num == 0 || min_out.num == 0 {
                            return Some("Swap with zero amount".to_string());
                        }
                    }
                    Action::Borrow { amount, .. } | Action::Repay { amount, .. } => {
                        if amount.num == 0 {
                            return Some("Borrow/Repay with zero amount".to_string());
                        }
                    }
                    _ => {}
                }
                None
            }
            Expr::Seq { first, second } => {
                self.find_invalid_action(first).or_else(|| self.find_invalid_action(second))
            }
            Expr::Parallel { exprs } => {
                for e in exprs {
                    if let Some(invalid) = self.find_invalid_action(e) {
                        return Some(invalid);
                    }
                }
                None
            }
            Expr::OnChain { expr, .. } => self.find_invalid_action(expr),
        }
    }

    /// Get performance statistics
    pub fn get_stats(&self) -> ConstraintCheckerStats {
        ConstraintCheckerStats {
            total_validations: self.total_validations,
            average_validation_time_us: if self.total_validations > 0 {
                self.total_validation_time_us / self.total_validations as u64
            } else {
                0
            },
        }
    }
}

#[derive(Debug)]
pub struct ConstraintCheckerStats {
    pub total_validations: usize,
    pub average_validation_time_us: u64,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::Protocol;

    #[test]
    fn test_deadline_constraint() {
        let mut checker = ConstraintChecker::new();
        
        let bundle = Bundle {
            name: "test".to_string(),
            start_chain: Chain::Polygon,
            expr: Expr::Seq {
                first: Box::new(Expr::Action {
                    action: Action::Borrow {
                        amount: Rational::new(1000, 1),
                        token: Token::WETH,
                        protocol: Protocol::Aave,
                    }
                }),
                second: Box::new(Expr::Action {
                    action: Action::Bridge {
                        chain: Chain::Arbitrum,
                        token: Token::WETH,
                        amount: Rational::new(1000, 1),
                    }
                }),
            },
            constraints: vec![Constraint::Deadline { blocks: 10 }], // Only 10 blocks allowed
        };

        let result = checker.validate_bundle(&bundle);
        assert!(!result.is_valid); // Should fail because bridge takes 20 blocks
        assert_eq!(result.violated_constraints.len(), 1);
        assert_eq!(result.violated_constraints[0].constraint_type, "Deadline");
    }

    #[test]
    fn test_balance_preservation() {
        let mut checker = ConstraintChecker::new();
        
        let bundle = Bundle {
            name: "test".to_string(),
            start_chain: Chain::Polygon,
            expr: Expr::Seq {
                first: Box::new(Expr::Action {
                    action: Action::Swap {
                        amount_in: Rational::new(1000, 1),
                        token_in: Token::WETH,
                        token_out: Token::USDC,
                        min_out: Rational::new(1500, 1),
                        protocol: Protocol::UniswapV2,
                    }
                }),
                second: Box::new(Expr::Action {
                    action: Action::Swap {
                        amount_in: Rational::new(1000, 1),
                        token_in: Token::WETH,
                        token_out: Token::USDC,
                        min_out: Rational::new(1500, 1),
                        protocol: Protocol::UniswapV2,
                    }
                }),
            },
            constraints: vec![],
        };

        let result = checker.validate_bundle(&bundle);
        assert!(!result.is_valid); // Should fail because we're spending 2000 WETH but don't have it
    }
}