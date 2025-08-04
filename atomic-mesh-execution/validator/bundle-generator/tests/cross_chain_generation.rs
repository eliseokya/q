//! Tests for cross-chain pattern generation

use bundle_generator::*;
use bundle_generator::patterns::CrossChainPatternGenerator;
use bundle_generator::registry::ProtocolRegistry;
use bundle_generator::bridges::{BridgeRegistry, BridgeInfo, BridgeCapability, Bridge};
use common::types::{Chain, Protocol, Token, Action, Rational};
use std::sync::Arc;
use std::collections::HashMap;

fn create_test_registries() -> (Arc<ProtocolRegistry>, Arc<BridgeRegistry>) {
    // Create protocol registry
    let mut protocol_registry = ProtocolRegistry::new();
    
    // Register Uniswap on both chains
    protocol_registry.register_protocol(
        Protocol::UniswapV2,
        Chain::Polygon,
        ProtocolInfo {
            address: "0xa5E0829CaCEd8fFDD4De3c43696c57F7D7A678ff".to_string(),
            abi_name: "uniswap_v2_router".to_string(),
            version: "2.0".to_string(),
            flash_loan_fee: Some(0.003),
        },
    );
    
    protocol_registry.register_protocol(
        Protocol::UniswapV2,
        Chain::Arbitrum,
        ProtocolInfo {
            address: "0x1b02dA8Cb0d097eB8D57A175b88c7D8b47997506".to_string(),
            abi_name: "uniswap_v2_router".to_string(),
            version: "2.0".to_string(),
            flash_loan_fee: Some(0.003),
        },
    );
    
    // Create bridge registry
    let mut bridge_registry = BridgeRegistry::new();
    
    // Register AtomicMesh bridge on both chains
    let mut min_amounts = HashMap::new();
    min_amounts.insert(Token::WETH, "100000000000000000".to_string());
    min_amounts.insert(Token::USDC, "100000000".to_string());
    
    let mut max_amounts = HashMap::new();
    max_amounts.insert(Token::WETH, "100000000000000000000".to_string());
    max_amounts.insert(Token::USDC, "1000000000000".to_string());
    
    bridge_registry.register_bridge(BridgeInfo {
        bridge: Bridge::AtomicMesh,
        chain: Chain::Polygon,
        contract_address: "0x1234567890123456789012345678901234567890".to_string(),
        version: "1.0".to_string(),
        capabilities: BridgeCapability {
            bridge: Bridge::AtomicMesh,
            supported_tokens: vec![Token::WETH, Token::USDC],
            supported_chains: vec![Chain::Polygon, Chain::Arbitrum],
            min_amount: min_amounts.clone(),
            max_amount: max_amounts.clone(),
            estimated_time_seconds: 120,
            base_fee: "10000000".to_string(),
            percentage_fee: 0.001,
        },
    });
    
    bridge_registry.register_bridge(BridgeInfo {
        bridge: Bridge::AtomicMesh,
        chain: Chain::Arbitrum,
        contract_address: "0x0987654321098765432109876543210987654321".to_string(),
        version: "1.0".to_string(),
        capabilities: BridgeCapability {
            bridge: Bridge::AtomicMesh,
            supported_tokens: vec![Token::WETH, Token::USDC],
            supported_chains: vec![Chain::Polygon, Chain::Arbitrum],
            min_amount: min_amounts,
            max_amount: max_amounts,
            estimated_time_seconds: 120,
            base_fee: "10000000".to_string(),
            percentage_fee: 0.001,
        },
    });
    
    (Arc::new(protocol_registry), Arc::new(bridge_registry))
}

#[test]
fn test_cross_chain_generation_basic() {
    let (protocol_registry, bridge_registry) = create_test_registries();
    let generator = CrossChainPatternGenerator::new(protocol_registry, bridge_registry);
    
    let params = PatternParameters {
        pattern_id: "cross-chain-arbitrage".to_string(),
        chain: Chain::Polygon,
        flash_loan_amount: None,
        flash_loan_token: None,
        flash_loan_protocol: None,
        operations: vec![
            // Swap WETH to USDC on Polygon
            Action::Swap {
                amount_in: Rational::from_integer(1000000000000000000), // 1 WETH
                token_in: Token::WETH,
                token_out: Token::USDC,
                min_out: Rational::from_integer(1500000000), // 1500 USDC
                protocol: Protocol::UniswapV2,
            },
            // Bridge USDC to Arbitrum
            Action::Bridge {
                chain: Chain::Arbitrum,
                token: Token::USDC,
                amount: Rational::from_integer(1500000000),
            },
            // Swap USDC back to WETH on Arbitrum
            Action::Swap {
                amount_in: Rational::from_integer(1500000000),
                token_in: Token::USDC,
                token_out: Token::WETH,
                min_out: Rational::from_integer(1010000000000000000), // 1.01 WETH
                protocol: Protocol::UniswapV2,
            },
        ],
        constraints: vec![],
    };
    
    let result = generator.generate(&params);
    assert!(result.is_ok());
    
    let bundle = result.unwrap();
    assert_eq!(bundle.pattern_id, "cross-chain-arbitrage");
    assert_eq!(bundle.validated, true);
    assert!(bundle.atomicity_proof.contains("CrossChain.lean"));
    
    // Check execution plan
    assert_eq!(bundle.execution_plan.total_steps, 3); // swap, bridge, swap
    
    // Verify operations order
    let ops = &bundle.execution_plan.operations;
    
    // First operation: swap on Polygon
    match &ops[0].operation {
        OperationType::Swap { dex, token_in, token_out, .. } => {
            assert_eq!(dex, &Protocol::UniswapV2);
            assert_eq!(token_in, &Token::WETH);
            assert_eq!(token_out, &Token::USDC);
            assert_eq!(ops[0].chain, Chain::Polygon);
        }
        _ => panic!("First operation should be swap"),
    }
    
    // Second operation: bridge to Arbitrum
    match &ops[1].operation {
        OperationType::Bridge { from_chain, to_chain, token, .. } => {
            assert_eq!(from_chain, &Chain::Polygon);
            assert_eq!(to_chain, &Chain::Arbitrum);
            assert_eq!(token, &Token::USDC);
        }
        _ => panic!("Second operation should be bridge"),
    }
    
    // Third operation: swap on Arbitrum
    match &ops[2].operation {
        OperationType::Swap { dex, token_in, token_out, .. } => {
            assert_eq!(dex, &Protocol::UniswapV2);
            assert_eq!(token_in, &Token::USDC);
            assert_eq!(token_out, &Token::WETH);
            assert_eq!(ops[2].chain, Chain::Arbitrum);
        }
        _ => panic!("Third operation should be swap"),
    }
    
    // Check gas is tracked per chain
    assert!(bundle.gas_config.gas_by_chain.contains_key(&Chain::Polygon));
    assert!(bundle.gas_config.gas_by_chain.contains_key(&Chain::Arbitrum));
}

#[test]
fn test_cross_chain_validation() {
    let (protocol_registry, bridge_registry) = create_test_registries();
    let generator = CrossChainPatternGenerator::new(protocol_registry, bridge_registry);
    
    // Test missing bridge operation
    let params = PatternParameters {
        pattern_id: "cross-chain-arbitrage".to_string(),
        chain: Chain::Polygon,
        flash_loan_amount: None,
        flash_loan_token: None,
        flash_loan_protocol: None,
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
    
    let result = generator.validate_feasibility(&params);
    assert!(result.is_err());
    assert!(result.unwrap_err().to_string().contains("requires at least one bridge"));
    
    // Test unavailable bridge route (WBTC not supported in our test registry)
    let params = PatternParameters {
        pattern_id: "cross-chain-arbitrage".to_string(),
        chain: Chain::Polygon,
        flash_loan_amount: None,
        flash_loan_token: None,
        flash_loan_protocol: None,
        operations: vec![
            Action::Bridge {
                chain: Chain::Arbitrum,
                token: Token::WBTC,
                amount: Rational::from_integer(100000000),
            }
        ],
        constraints: vec![],
    };
    
    let result = generator.validate_feasibility(&params);
    assert!(result.is_err());
    assert!(result.unwrap_err().to_string().contains("Bridge unavailable"));
}

#[test]
fn test_cross_chain_gas_estimation() {
    let (protocol_registry, bridge_registry) = create_test_registries();
    let generator = CrossChainPatternGenerator::new(protocol_registry, bridge_registry);
    
    let params = PatternParameters {
        pattern_id: "cross-chain-arbitrage".to_string(),
        chain: Chain::Polygon,
        flash_loan_amount: None,
        flash_loan_token: None,
        flash_loan_protocol: None,
        operations: vec![
            Action::Bridge {
                chain: Chain::Arbitrum,
                token: Token::WETH,
                amount: Rational::from_integer(1000000000000000000),
            }
        ],
        constraints: vec![],
    };
    
    let gas_result = generator.estimate_gas(&params);
    assert!(gas_result.is_ok());
    
    let gas = gas_result.unwrap();
    assert!(gas >= 300_000); // Bridge operations are expensive
}

#[test]
fn test_cross_chain_timing() {
    let (protocol_registry, bridge_registry) = create_test_registries();
    let generator = CrossChainPatternGenerator::new(protocol_registry, bridge_registry);
    
    let params = PatternParameters {
        pattern_id: "cross-chain-arbitrage".to_string(),
        chain: Chain::Polygon,
        flash_loan_amount: None,
        flash_loan_token: None,
        flash_loan_protocol: None,
        operations: vec![
            Action::Bridge {
                chain: Chain::Arbitrum,
                token: Token::WETH,
                amount: Rational::from_integer(1000000000000000000),
            }
        ],
        constraints: vec![],
    };
    
    let bundle = generator.generate(&params).unwrap();
    
    // Should include bridge time (120s) + buffer (60s)
    assert!(bundle.execution_plan.estimated_duration >= 180);
}