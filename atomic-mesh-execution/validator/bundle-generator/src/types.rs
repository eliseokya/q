//! Core types for the Bundle Generator module

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use common::types::{Chain, Protocol, Token};

/// Type alias for Ethereum addresses
pub type Address = String;

/// Main execution bundle output structure
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionBundle {
    pub bundle_id: String,
    pub opportunity_id: String,
    pub pattern_id: String,
    pub validated: bool,
    pub atomicity_proof: String,
    pub execution_plan: ExecutionPlan,
    pub gas_config: GasConfig,
    pub profit_config: ProfitConfig,
    pub contracts: HashMap<Chain, ChainContracts>,
    pub optimization_hints: OptimizationHints,
}

/// Execution plan with ordered operations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionPlan {
    pub total_steps: u32,
    pub estimated_duration: u64, // in seconds
    pub operations: Vec<ExecutionStep>,
}

/// Individual execution step
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionStep {
    pub step_number: u32,
    pub operation: OperationType,
    pub chain: Chain,
    pub contract: Address,
    pub function: String,
    pub params: serde_json::Value,
    pub gas_estimate: u64,
    pub dependencies: Vec<u32>, // step numbers this depends on
}

/// Types of operations in execution
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum OperationType {
    FlashLoan {
        protocol: Protocol,
        asset: Token,
        amount: String,
    },
    FlashLoanCallback,
    Swap {
        dex: Protocol,
        token_in: Token,
        token_out: Token,
        amount_in: String,
        min_amount_out: String,
    },
    Bridge {
        bridge_protocol: String,
        token: Token,
        amount: String,
        from_chain: Chain,
        to_chain: Chain,
    },
    Repay {
        protocol: Protocol,
        asset: Token,
        amount: String,
    },
}

/// Gas configuration and estimates
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GasConfig {
    pub total_gas_estimate: u64,
    pub gas_by_chain: HashMap<Chain, u64>,
    pub gas_price_gwei: HashMap<Chain, f64>,
    pub gas_optimization_applied: bool,
    pub savings_percent: f64,
}

/// Profit configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProfitConfig {
    pub expected_profit: String,
    pub min_profit_threshold: String,
    pub profit_token: Token,
    pub profit_receiver: Address,
}

/// Chain-specific contract addresses
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChainContracts {
    pub executor: Address,
    pub protocols: HashMap<Protocol, Address>,
}

/// Optimization hints for execution
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OptimizationHints {
    pub pattern_type: String,
    pub parallelizable_steps: Vec<Vec<u32>>,
    pub critical_path: Vec<u32>,
    pub gas_optimization_potential: f64,
}

/// Parameters extracted from pattern match
#[derive(Debug, Clone)]
pub struct PatternParameters {
    pub pattern_id: String,
    pub chain: Chain,
    pub flash_loan_amount: Option<String>,
    pub flash_loan_token: Option<Token>,
    pub flash_loan_protocol: Option<Protocol>,
    pub operations: Vec<common::types::Action>,
    pub constraints: Vec<common::types::Constraint>,
}

/// Protocol information from registry
#[derive(Debug, Clone, Deserialize)]
pub struct ProtocolInfo {
    pub address: Address,
    pub abi_name: String,
    pub version: String,
    pub flash_loan_fee: Option<f64>,
}

/// Result of bundle generation
pub type BundleResult = Result<ExecutionBundle, BundleGeneratorError>;

/// Bundle generator errors
#[derive(Debug, thiserror::Error)]
pub enum BundleGeneratorError {
    #[error("Unknown pattern: {0}")]
    UnknownPattern(String),
    
    #[error("Protocol not found: {protocol} on {chain:?}")]
    ProtocolNotFound { protocol: String, chain: Chain },
    
    #[error("Bridge unavailable: {token:?} from {from:?} to {to:?}")]
    BridgeUnavailable { token: Token, from: Chain, to: Chain },
    
    #[error("Gas estimate exceeded: estimated {estimated}, limit {limit}")]
    GasEstimateExceeded { estimated: u64, limit: u64 },
    
    #[error("Insufficient liquidity: required {required}, available {available}")]
    InsufficientLiquidity { required: String, available: String },
    
    #[error("Configuration error: {0}")]
    ConfigError(String),
    
    #[error("Encoding error: {0}")]
    EncodingError(String),
    
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),
}