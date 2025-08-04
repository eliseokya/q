//! Common utilities for pattern generators

use uuid::Uuid;
use chrono::Utc;
use common::types::Chain;
use crate::types::{ExecutionStep, OperationType, Address};

/// Generate a unique bundle ID
pub fn generate_bundle_id() -> String {
    format!("bundle_{}", Uuid::new_v4())
}

/// Generate a timestamp
pub fn current_timestamp() -> u64 {
    Utc::now().timestamp() as u64
}

/// Estimate gas for common operations
pub fn estimate_operation_gas(op: &OperationType, chain: Chain) -> u64 {
    match op {
        OperationType::FlashLoan { .. } => match chain {
            Chain::Polygon => 180_000,
            Chain::Arbitrum => 150_000,
        },
        OperationType::FlashLoanCallback => 50_000,
        OperationType::Swap { .. } => match chain {
            Chain::Polygon => 200_000,
            Chain::Arbitrum => 180_000,
        },
        OperationType::Bridge { .. } => 300_000,
        OperationType::Repay { .. } => 100_000,
    }
}

/// Calculate total gas for a sequence of operations
pub fn calculate_total_gas(steps: &[ExecutionStep]) -> u64 {
    steps.iter().map(|step| step.gas_estimate).sum()
}

/// Build dependencies for sequential operations
pub fn build_sequential_dependencies(num_steps: u32) -> Vec<Vec<u32>> {
    (0..num_steps)
        .map(|i| if i > 0 { vec![i - 1] } else { vec![] })
        .collect()
}

/// Format token amount with decimals
pub fn format_amount(amount: u128, _decimals: u8) -> String {
    amount.to_string()
}

/// Get common contract addresses
pub fn get_executor_address(chain: Chain) -> Address {
    // In production, these would be deployed contract addresses
    match chain {
        Chain::Polygon => "0x0000000000000000000000000000000000000002".to_string(),
        Chain::Arbitrum => "0x0000000000000000000000000000000000000003".to_string(),
    }
}