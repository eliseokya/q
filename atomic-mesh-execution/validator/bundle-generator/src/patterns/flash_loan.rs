//! Flash loan pattern generator for Aave V3

use std::sync::Arc;
use std::collections::HashMap;
use serde_json::json;
use common::types::{Chain, Protocol, Token, Action};
use crate::types::*;
use crate::traits::PatternBundleGenerator;
use crate::registry::ProtocolRegistry;
use crate::error::{Result, BundleGeneratorError};
use crate::patterns::common::*;

/// Flash loan pattern generator for atomic arbitrage
pub struct FlashLoanPatternGenerator {
    protocol_registry: Arc<ProtocolRegistry>,
}

impl FlashLoanPatternGenerator {
    /// Create a new flash loan pattern generator
    pub fn new(protocol_registry: Arc<ProtocolRegistry>) -> Self {
        Self { protocol_registry }
    }
    
    /// Calculate repayment amount including fee
    fn calculate_repayment(&self, amount: &str, protocol: Protocol, chain: Chain) -> Result<String> {
        let fee = self.protocol_registry
            .get_flash_loan_fee(protocol, chain)?
            .unwrap_or(0.0);
        
        // Parse amount (in production, use proper decimal handling)
        let amount_val: u128 = amount.parse()
            .map_err(|_| BundleGeneratorError::EncodingError("Invalid amount".to_string()))?;
        
        let fee_amount = (amount_val as f64 * fee) as u128;
        let total = amount_val + fee_amount;
        
        Ok(total.to_string())
    }
    
    /// Build flash loan initiation parameters
    fn build_flash_loan_params(
        &self,
        asset: &Token,
        amount: &str,
        receiver: &str,
    ) -> serde_json::Value {
        // Aave V3 flashLoan parameters
        json!({
            "assets": [format!("{:?}", asset)],  // In production, use actual token addresses
            "amounts": [amount],
            "interestRateModes": [0],  // 0 = no debt
            "onBehalfOf": receiver,
            "params": "0x",  // Empty params for simple flash loan
            "referralCode": 0
        })
    }
    
    /// Generate execution steps from pattern parameters
    fn generate_steps(&self, params: &PatternParameters) -> Result<Vec<ExecutionStep>> {
        let chain = params.chain.clone();
        let flash_loan_protocol = params.flash_loan_protocol.clone()
            .ok_or_else(|| BundleGeneratorError::ConfigError("Missing flash loan protocol".to_string()))?;
        let flash_loan_token = params.flash_loan_token.clone()
            .ok_or_else(|| BundleGeneratorError::ConfigError("Missing flash loan token".to_string()))?;
        let flash_loan_amount = params.flash_loan_amount
            .as_ref()
            .ok_or_else(|| BundleGeneratorError::ConfigError("Missing flash loan amount".to_string()))?;
        
        let mut steps = Vec::new();
        let mut step_number = 1;
        
        // Step 1: Flash loan initiation
        let flash_loan_contract = self.protocol_registry
            .get_contract(flash_loan_protocol.clone(), chain.clone())?;
        
        steps.push(ExecutionStep {
            step_number,
            operation: OperationType::FlashLoan {
                protocol: flash_loan_protocol.clone(),
                asset: flash_loan_token.clone(),
                amount: flash_loan_amount.clone(),
            },
            chain: chain.clone(),
            contract: flash_loan_contract.clone(),
            function: "flashLoan".to_string(),
            params: self.build_flash_loan_params(
                &flash_loan_token,
                flash_loan_amount,
                &get_executor_address(chain.clone()),
            ),
            gas_estimate: estimate_operation_gas(
                &OperationType::FlashLoan {
                    protocol: flash_loan_protocol.clone(),
                    asset: flash_loan_token.clone(),
                    amount: flash_loan_amount.clone(),
                },
                chain.clone(),
            ),
            dependencies: vec![],
        });
        step_number += 1;
        
        // Step 2: Flash loan callback starts
        steps.push(ExecutionStep {
            step_number,
            operation: OperationType::FlashLoanCallback,
            chain: chain.clone(),
            contract: get_executor_address(chain.clone()),
            function: "executeOperation".to_string(),
            params: json!({}),
            gas_estimate: estimate_operation_gas(&OperationType::FlashLoanCallback, chain.clone()),
            dependencies: vec![step_number - 1],
        });
        step_number += 1;
        
        // Steps 3-N: User operations (swaps, bridges, etc.)
        for action in &params.operations {
            match action {
                Action::Swap { amount_in, token_in, token_out, min_out, protocol } => {
                    // In production, get actual DEX router addresses
                    let dex_contract = self.protocol_registry
                        .get_contract(protocol.clone(), chain.clone())
                        .unwrap_or_else(|_| "0x0000000000000000000000000000000000000000".to_string());
                    
                    steps.push(ExecutionStep {
                        step_number,
                        operation: OperationType::Swap {
                            dex: protocol.clone(),
                            token_in: token_in.clone(),
                            token_out: token_out.clone(),
                            amount_in: format!("{}", amount_in.num), // Simple conversion for now
                            min_amount_out: format!("{}", min_out.num),
                        },
                        chain: chain.clone(),
                        contract: dex_contract,
                        function: "swap".to_string(),
                        params: json!({
                            "tokenIn": format!("{:?}", token_in),
                            "tokenOut": format!("{:?}", token_out),
                            "amountIn": format!("{}", amount_in.num),
                            "amountOutMin": format!("{}", min_out.num),
                            "recipient": get_executor_address(chain.clone()),
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
                            chain.clone(),
                        ),
                        dependencies: vec![step_number - 1],
                    });
                    step_number += 1;
                }
                _ => {
                    // Handle other action types in future phases
                }
            }
        }
        
        // Final step: Repay flash loan
        let repayment_amount = self.calculate_repayment(
            flash_loan_amount,
            flash_loan_protocol.clone(),
            chain.clone(),
        )?;
        
        steps.push(ExecutionStep {
            step_number,
            operation: OperationType::Repay {
                protocol: flash_loan_protocol.clone(),
                asset: flash_loan_token.clone(),
                amount: repayment_amount.clone(),
            },
            chain: chain.clone(),
            contract: flash_loan_contract,
            function: "repay".to_string(),
            params: json!({
                "asset": format!("{:?}", flash_loan_token),
                "amount": repayment_amount,
                "interestRateMode": 0,
                "onBehalfOf": get_executor_address(chain.clone()),
            }),
            gas_estimate: estimate_operation_gas(
                &OperationType::Repay {
                    protocol: flash_loan_protocol,
                    asset: flash_loan_token,
                    amount: repayment_amount,
                },
                chain.clone(),
            ),
            dependencies: vec![step_number - 1],
        });
        
        Ok(steps)
    }
}

impl PatternBundleGenerator for FlashLoanPatternGenerator {
    fn generate(&self, params: &PatternParameters) -> Result<ExecutionBundle> {
        // Validate parameters
        self.validate_feasibility(params)?;
        
        // Generate execution steps
        let steps = self.generate_steps(params)?;
        let total_gas = calculate_total_gas(&steps);
        
        // Build gas configuration
        let mut gas_by_chain = HashMap::new();
        gas_by_chain.insert(params.chain.clone(), total_gas);
        
        let gas_config = GasConfig {
            total_gas_estimate: total_gas,
            gas_by_chain,
            gas_price_gwei: HashMap::new(), // Will be populated by gas oracle in future
            gas_optimization_applied: false,
            savings_percent: 0.0,
        };
        
        // Build contracts map
        let mut chain_contracts = HashMap::new();
        let mut protocols = HashMap::new();
        
        if let Some(protocol) = &params.flash_loan_protocol {
            let address = self.protocol_registry.get_contract(protocol.clone(), params.chain.clone())?;
            protocols.insert(protocol.clone(), address);
        }
        
        chain_contracts.insert(params.chain.clone(), ChainContracts {
            executor: get_executor_address(params.chain.clone()),
            protocols,
        });
        
        // Build execution bundle
        let bundle = ExecutionBundle {
            bundle_id: generate_bundle_id(),
            opportunity_id: params.pattern_id.clone(),
            pattern_id: self.pattern_id().to_string(),
            validated: true,
            atomicity_proof: "maths/DSL/Patterns/FlashLoan.lean:theorem_flash_loan_atomic".to_string(),
            execution_plan: ExecutionPlan {
                total_steps: steps.len() as u32,
                estimated_duration: 180, // ~3 minutes for flash loan
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
                pattern_type: "flash_loan".to_string(),
                parallelizable_steps: vec![],
                critical_path: vec![1, 2, steps.len() as u32],
                gas_optimization_potential: 0.3,
            },
        };
        
        Ok(bundle)
    }
    
    fn estimate_gas(&self, params: &PatternParameters) -> Result<u64> {
        let steps = self.generate_steps(params)?;
        Ok(calculate_total_gas(&steps))
    }
    
    fn validate_feasibility(&self, params: &PatternParameters) -> Result<()> {
        // Validate flash loan protocol is supported
        if let Some(protocol) = &params.flash_loan_protocol {
            if !self.protocol_registry.is_supported(protocol.clone(), params.chain.clone()) {
                return Err(BundleGeneratorError::ProtocolNotFound {
                    protocol: format!("{:?}", protocol),
                    chain: params.chain.clone(),
                });
            }
        } else {
            return Err(BundleGeneratorError::ConfigError(
                "Flash loan pattern requires flash loan protocol".to_string()
            ));
        }
        
        // Validate required parameters
        if params.flash_loan_amount.is_none() {
            return Err(BundleGeneratorError::ConfigError(
                "Flash loan pattern requires loan amount".to_string()
            ));
        }
        
        if params.flash_loan_token.is_none() {
            return Err(BundleGeneratorError::ConfigError(
                "Flash loan pattern requires loan token".to_string()
            ));
        }
        
        Ok(())
    }
    
    fn pattern_id(&self) -> &str {
        "flash-loan-arbitrage"
    }
}