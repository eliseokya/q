//! Tests for type serialization and deserialization

use bundle_generator::*;
use serde_json;
use common::types::{Chain, Protocol, Token};
use std::collections::HashMap;

#[test]
fn test_execution_bundle_serialization() {
    let mut gas_by_chain = HashMap::new();
    gas_by_chain.insert(Chain::Polygon, 500_000);
    
    let mut protocols = HashMap::new();
    protocols.insert(Protocol::Aave, "0x794a61358D6845594F94dc1DB02A252b5b4814aD".to_string());
    
    let mut contracts = HashMap::new();
    contracts.insert(Chain::Polygon, ChainContracts {
        executor: "0x0000000000000000000000000000000000000002".to_string(),
        protocols,
    });
    
    let bundle = ExecutionBundle {
        bundle_id: "bundle_123".to_string(),
        opportunity_id: "opp_123".to_string(),
        pattern_id: "flash-loan-arbitrage".to_string(),
        validated: true,
        atomicity_proof: "maths/DSL/Patterns/FlashLoan.lean:theorem_2.3".to_string(),
        execution_plan: ExecutionPlan {
            total_steps: 4,
            estimated_duration: 180,
            operations: vec![
                ExecutionStep {
                    step_number: 1,
                    operation: OperationType::FlashLoan {
                        protocol: Protocol::Aave,
                        asset: Token::WETH,
                        amount: "1000000000000000000".to_string(),
                    },
                    chain: Chain::Polygon,
                    contract: "0x794a61358D6845594F94dc1DB02A252b5b4814aD".to_string(),
                    function: "flashLoan".to_string(),
                    params: serde_json::json!({
                        "assets": ["WETH"],
                        "amounts": ["1000000000000000000"],
                    }),
                    gas_estimate: 180_000,
                    dependencies: vec![],
                }
            ],
        },
        gas_config: GasConfig {
            total_gas_estimate: 500_000,
            gas_by_chain,
            gas_price_gwei: HashMap::new(),
            gas_optimization_applied: false,
            savings_percent: 0.0,
        },
        profit_config: ProfitConfig {
            expected_profit: "1000".to_string(),
            min_profit_threshold: "100".to_string(),
            profit_token: Token::USDC,
            profit_receiver: "0x0000000000000000000000000000000000000002".to_string(),
        },
        contracts,
        optimization_hints: OptimizationHints {
            pattern_type: "flash_loan".to_string(),
            parallelizable_steps: vec![],
            critical_path: vec![1, 2, 4],
            gas_optimization_potential: 0.3,
        },
    };
    
    // Serialize
    let json = serde_json::to_string_pretty(&bundle).unwrap();
    
    // Deserialize
    let deserialized: ExecutionBundle = serde_json::from_str(&json).unwrap();
    
    // Verify
    assert_eq!(deserialized.bundle_id, bundle.bundle_id);
    assert_eq!(deserialized.pattern_id, bundle.pattern_id);
    assert_eq!(deserialized.execution_plan.total_steps, 4);
    assert_eq!(deserialized.gas_config.total_gas_estimate, 500_000);
}

#[test]
fn test_operation_type_serialization() {
    let operations = vec![
        OperationType::FlashLoan {
            protocol: Protocol::Aave,
            asset: Token::WETH,
            amount: "1000".to_string(),
        },
        OperationType::Swap {
            dex: Protocol::UniswapV2,
            token_in: Token::WETH,
            token_out: Token::USDC,
            amount_in: "1000".to_string(),
            min_amount_out: "1500000".to_string(),
        },
        OperationType::FlashLoanCallback,
    ];
    
    for op in operations {
        let json = serde_json::to_string(&op).unwrap();
        let deserialized: OperationType = serde_json::from_str(&json).unwrap();
        
        match (&op, &deserialized) {
            (OperationType::FlashLoan { protocol: p1, .. }, 
             OperationType::FlashLoan { protocol: p2, .. }) => {
                assert_eq!(p1, p2);
            }
            (OperationType::Swap { dex: d1, .. }, 
             OperationType::Swap { dex: d2, .. }) => {
                assert_eq!(d1, d2);
            }
            (OperationType::FlashLoanCallback, OperationType::FlashLoanCallback) => {}
            _ => panic!("Operation type mismatch"),
        }
    }
}