//! Cross-chain arbitrage pattern generator

use std::sync::Arc;
use std::collections::HashMap;
use serde_json::json;
use common::types::{Token, Action};
use crate::types::*;
use crate::traits::PatternBundleGenerator;
use crate::registry::ProtocolRegistry;
use crate::bridges::{BridgeRouter, BridgeRegistry, BridgeSelectionCriteria};
use crate::error::{Result, BundleGeneratorError};
use crate::patterns::common::*;

/// Cross-chain arbitrage pattern generator
pub struct CrossChainPatternGenerator {
    protocol_registry: Arc<ProtocolRegistry>,
    bridge_router: Arc<BridgeRouter>,
}

impl CrossChainPatternGenerator {
    /// Create a new cross-chain pattern generator
    pub fn new(
        protocol_registry: Arc<ProtocolRegistry>,
        bridge_registry: Arc<BridgeRegistry>,
    ) -> Self {
        let bridge_router = Arc::new(BridgeRouter::new(bridge_registry));
        Self {
            protocol_registry,
            bridge_router,
        }
    }
    
    /// Generate execution steps for cross-chain arbitrage
    fn generate_steps(&self, params: &PatternParameters) -> Result<Vec<ExecutionStep>> {
        let mut steps = Vec::new();
        let mut step_number = 1;
        let mut current_chain = params.chain.clone();
        
        // Track which chains we need to operate on
        let mut chains_involved = vec![current_chain.clone()];
        
        // Process all operations and identify cross-chain requirements
        for action in &params.operations {
            match action {
                Action::Bridge { chain, token, amount } => {
                    // Find best bridge route
                    let bridge_route = self.bridge_router.find_best_route(
                        current_chain.clone(),
                        chain.clone(),
                        token.clone(),
                        &format!("{}", amount.num),
                        &BridgeSelectionCriteria::default(),
                    )?;
                    
                    // Step: Initiate bridge on source chain
                    steps.push(ExecutionStep {
                        step_number,
                        operation: OperationType::Bridge {
                            bridge_protocol: format!("{:?}", bridge_route.bridge),
                            token: token.clone(),
                            amount: format!("{}", amount.num),
                            from_chain: current_chain.clone(),
                            to_chain: chain.clone(),
                        },
                        chain: current_chain.clone(),
                        contract: bridge_route.contract_from.clone(),
                        function: "bridge".to_string(),
                        params: json!({
                            "token": format!("{:?}", token),
                            "amount": format!("{}", amount.num),
                            "toChain": format!("{:?}", chain),
                            "recipient": get_executor_address(chain.clone()),
                            "data": "0x"
                        }),
                        gas_estimate: 300_000, // Bridge operations are gas-intensive
                        dependencies: if step_number > 1 { vec![step_number - 1] } else { vec![] },
                    });
                    step_number += 1;
                    
                    // Update current chain
                    current_chain = chain.clone();
                    if !chains_involved.contains(&current_chain) {
                        chains_involved.push(current_chain.clone());
                    }
                }
                
                Action::Swap { amount_in, token_in, token_out, min_out, protocol } => {
                    // Regular swap on current chain
                    let dex_contract = self.protocol_registry
                        .get_contract(protocol.clone(), current_chain.clone())
                        .unwrap_or_else(|_| "0x0000000000000000000000000000000000000000".to_string());
                    
                    steps.push(ExecutionStep {
                        step_number,
                        operation: OperationType::Swap {
                            dex: protocol.clone(),
                            token_in: token_in.clone(),
                            token_out: token_out.clone(),
                            amount_in: format!("{}", amount_in.num),
                            min_amount_out: format!("{}", min_out.num),
                        },
                        chain: current_chain.clone(),
                        contract: dex_contract,
                        function: "swap".to_string(),
                        params: json!({
                            "tokenIn": format!("{:?}", token_in),
                            "tokenOut": format!("{:?}", token_out),
                            "amountIn": format!("{}", amount_in.num),
                            "amountOutMin": format!("{}", min_out.num),
                            "recipient": get_executor_address(current_chain.clone()),
                            "deadline": 999999999999u64,
                        }),
                        gas_estimate: estimate_operation_gas(
                            &OperationType::Swap {
                                dex: protocol.clone(),
                                token_in: token_in.clone(),
                                token_out: token_out.clone(),
                                amount_in: format!("{}", amount_in.num),
                                min_amount_out: format!("{}", min_out.num),
                            },
                            current_chain.clone(),
                        ),
                        dependencies: if step_number > 1 { vec![step_number - 1] } else { vec![] },
                    });
                    step_number += 1;
                }
                
                Action::Borrow { amount, token, protocol } => {
                    // Flash loan on current chain
                    let flash_loan_contract = self.protocol_registry
                        .get_contract(protocol.clone(), current_chain.clone())?;
                    
                    steps.push(ExecutionStep {
                        step_number,
                        operation: OperationType::FlashLoan {
                            protocol: protocol.clone(),
                            asset: token.clone(),
                            amount: format!("{}", amount.num),
                        },
                        chain: current_chain.clone(),
                        contract: flash_loan_contract,
                        function: "flashLoan".to_string(),
                        params: json!({
                            "assets": [format!("{:?}", token)],
                            "amounts": [format!("{}", amount.num)],
                            "interestRateModes": [0],
                            "onBehalfOf": get_executor_address(current_chain.clone()),
                            "params": "0x",
                            "referralCode": 0
                        }),
                        gas_estimate: estimate_operation_gas(
                            &OperationType::FlashLoan {
                                protocol: protocol.clone(),
                                asset: token.clone(),
                                amount: format!("{}", amount.num),
                            },
                            current_chain.clone(),
                        ),
                        dependencies: if step_number > 1 { vec![step_number - 1] } else { vec![] },
                    });
                    step_number += 1;
                }
                
                _ => {
                    // Handle other action types in future
                }
            }
        }
        
        Ok(steps)
    }
    
    /// Calculate total bridge time for the pattern
    fn calculate_bridge_time(&self, params: &PatternParameters) -> u64 {
        let mut total_time = 0u64;
        let mut current_chain = params.chain.clone();
        
        for action in &params.operations {
            if let Action::Bridge { chain, token, amount } = action {
                if let Ok(route) = self.bridge_router.find_best_route(
                    current_chain.clone(),
                    chain.clone(),
                    token.clone(),
                    &format!("{}", amount.num),
                    &BridgeSelectionCriteria::default(),
                ) {
                    total_time += route.estimated_time;
                }
                current_chain = chain.clone();
            }
        }
        
        // Add buffer for confirmations
        total_time + 60
    }
}

impl PatternBundleGenerator for CrossChainPatternGenerator {
    fn generate(&self, params: &PatternParameters) -> Result<ExecutionBundle> {
        // Validate parameters
        self.validate_feasibility(params)?;
        
        // Generate execution steps
        let steps = self.generate_steps(params)?;
        let total_gas = calculate_total_gas(&steps);
        
        // Build gas configuration per chain
        let mut gas_by_chain = HashMap::new();
        for step in &steps {
            *gas_by_chain.entry(step.chain.clone()).or_insert(0) += step.gas_estimate;
        }
        
        let gas_config = GasConfig {
            total_gas_estimate: total_gas,
            gas_by_chain,
            gas_price_gwei: HashMap::new(),
            gas_optimization_applied: false,
            savings_percent: 0.0,
        };
        
        // Build contracts map for all involved chains
        let mut chain_contracts = HashMap::new();
        let mut seen_chains = std::collections::HashSet::new();
        
        for step in &steps {
            if seen_chains.insert(step.chain.clone()) {
                chain_contracts.insert(step.chain.clone(), ChainContracts {
                    executor: get_executor_address(step.chain.clone()),
                    protocols: HashMap::new(),
                });
            }
        }
        
        // Calculate estimated duration based on bridge times
        let estimated_duration = self.calculate_bridge_time(params);
        
        // Build execution bundle
        let bundle = ExecutionBundle {
            bundle_id: generate_bundle_id(),
            opportunity_id: params.pattern_id.clone(),
            pattern_id: self.pattern_id().to_string(),
            validated: true,
            atomicity_proof: "maths/DSL/Patterns/CrossChain.lean:theorem_cross_chain_atomic".to_string(),
            execution_plan: ExecutionPlan {
                total_steps: steps.len() as u32,
                estimated_duration,
                operations: steps.clone(),
            },
            gas_config,
            profit_config: ProfitConfig {
                expected_profit: "1000".to_string(), // Placeholder
                min_profit_threshold: "100".to_string(),
                profit_token: Token::USDC,
                profit_receiver: get_executor_address(params.chain.clone()),
            },
            contracts: chain_contracts,
            optimization_hints: OptimizationHints {
                pattern_type: "cross_chain".to_string(),
                parallelizable_steps: vec![], // Cross-chain is mostly sequential
                critical_path: (1..=steps.len() as u32).collect(),
                gas_optimization_potential: 0.2, // Less optimization possible due to bridges
            },
        };
        
        Ok(bundle)
    }
    
    fn estimate_gas(&self, params: &PatternParameters) -> Result<u64> {
        let steps = self.generate_steps(params)?;
        Ok(calculate_total_gas(&steps))
    }
    
    /// Validate that the pattern is feasible
    fn validate_feasibility(&self, params: &PatternParameters) -> Result<()> {
        // Check if pattern has bridge operations
        let has_bridge = params.operations.iter().any(|op| matches!(op, Action::Bridge { .. }));
        
        if !has_bridge {
            return Err(BundleGeneratorError::ConfigError(
                "Cross-chain pattern requires at least one bridge operation".to_string()
            ));
        }
        
        // Validate bridge routes exist
        let mut current_chain = params.chain.clone();
        for action in &params.operations {
            if let Action::Bridge { chain, token, amount: _ } = action {
                if !self.bridge_router.is_route_available(current_chain.clone(), chain.clone(), token.clone()) {
                    return Err(BundleGeneratorError::BridgeUnavailable {
                        token: token.clone(),
                        from: current_chain,
                        to: chain.clone(),
                    });
                }
                current_chain = chain.clone();
            }
        }
        
        Ok(())
    }
    
    fn pattern_id(&self) -> &str {
        "cross-chain-arbitrage"
    }
}