//! Tests for flash loan pattern generation

use bundle_generator::*;
use bundle_generator::patterns::FlashLoanPatternGenerator;
use bundle_generator::registry::ProtocolRegistry;
use common::types::{Chain, Protocol, Token, Action, Rational};
use std::sync::Arc;

fn create_test_registry() -> Arc<ProtocolRegistry> {
    let mut registry = ProtocolRegistry::new();
    
    // Register Aave on Polygon for testing
    registry.register_protocol(
        Protocol::Aave,
        Chain::Polygon,
        ProtocolInfo {
            address: "0x794a61358D6845594F94dc1DB02A252b5b4814aD".to_string(),
            abi_name: "aave_v3_pool".to_string(),
            version: "3.0".to_string(),
            flash_loan_fee: Some(0.0009),
        },
    );
    
    Arc::new(registry)
}

#[test]
fn test_flash_loan_generation_basic() {
    let registry = create_test_registry();
    let generator = FlashLoanPatternGenerator::new(registry);
    
    let params = PatternParameters {
        pattern_id: "flash-loan-arbitrage".to_string(),
        chain: Chain::Polygon,
        flash_loan_amount: Some("1000000000000000000".to_string()), // 1 WETH
        flash_loan_token: Some(Token::WETH),
        flash_loan_protocol: Some(Protocol::Aave),
        operations: vec![
            Action::Swap {
                amount_in: Rational::from_integer(1000000000000000000),
                token_in: Token::WETH,
                token_out: Token::USDC,
                min_out: Rational::from_integer(1500000000),
                protocol: Protocol::UniswapV2,
            }
        ],
        constraints: vec![],
    };
    
    let result = generator.generate(&params);
    assert!(result.is_ok());
    
    let bundle = result.unwrap();
    assert_eq!(bundle.pattern_id, "flash-loan-arbitrage");
    assert_eq!(bundle.validated, true);
    assert!(bundle.atomicity_proof.contains("FlashLoan.lean"));
    
    // Check execution plan
    assert!(bundle.execution_plan.total_steps >= 4); // Flash loan, callback, swap, repay
    
    // Verify first operation is flash loan
    if let Some(first_op) = bundle.execution_plan.operations.first() {
        match &first_op.operation {
            OperationType::FlashLoan { protocol, asset, amount } => {
                assert_eq!(protocol, &Protocol::Aave);
                assert_eq!(asset, &Token::WETH);
                assert_eq!(amount, "1000000000000000000");
            }
            _ => panic!("First operation should be flash loan"),
        }
    }
    
    // Verify last operation is repayment
    if let Some(last_op) = bundle.execution_plan.operations.last() {
        match &last_op.operation {
            OperationType::Repay { protocol, asset, amount } => {
                assert_eq!(protocol, &Protocol::Aave);
                assert_eq!(asset, &Token::WETH);
                // Amount should include fee (0.09%)
                let expected_repay = 1000000000000000000u128 + (1000000000000000000u128 * 9 / 10000);
                assert_eq!(amount, &expected_repay.to_string());
            }
            _ => panic!("Last operation should be repay"),
        }
    }
}

#[test]
fn test_flash_loan_gas_estimation() {
    let registry = create_test_registry();
    let generator = FlashLoanPatternGenerator::new(registry);
    
    let params = PatternParameters {
        pattern_id: "flash-loan-arbitrage".to_string(),
        chain: Chain::Polygon,
        flash_loan_amount: Some("1000000000000000000".to_string()),
        flash_loan_token: Some(Token::WETH),
        flash_loan_protocol: Some(Protocol::Aave),
        operations: vec![],
        constraints: vec![],
    };
    
    let gas_result = generator.estimate_gas(&params);
    assert!(gas_result.is_ok());
    
    let gas = gas_result.unwrap();
    assert!(gas > 0);
    assert!(gas < 1_000_000); // Should be reasonable
}

#[test]
fn test_flash_loan_validation() {
    let registry = create_test_registry();
    let generator = FlashLoanPatternGenerator::new(registry);
    
    // Test missing flash loan amount
    let params = PatternParameters {
        pattern_id: "flash-loan-arbitrage".to_string(),
        chain: Chain::Polygon,
        flash_loan_amount: None,
        flash_loan_token: Some(Token::WETH),
        flash_loan_protocol: Some(Protocol::Aave),
        operations: vec![],
        constraints: vec![],
    };
    
    let result = generator.validate_feasibility(&params);
    assert!(result.is_err());
    assert!(result.unwrap_err().to_string().contains("loan amount"));
    
    // Test unsupported protocol on different chain
    let params = PatternParameters {
        pattern_id: "flash-loan-arbitrage".to_string(),
        chain: Chain::Arbitrum, // Not registered in test registry
        flash_loan_amount: Some("1000".to_string()),
        flash_loan_token: Some(Token::WETH),
        flash_loan_protocol: Some(Protocol::Aave),
        operations: vec![],
        constraints: vec![],
    };
    
    let result = generator.validate_feasibility(&params);
    assert!(result.is_err());
    assert!(result.unwrap_err().to_string().contains("Protocol not found"));
}