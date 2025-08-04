//! Example demonstrating cross-chain bundle generation

use bundle_generator::*;
use std::path::Path;

fn main() -> Result<()> {
    // Initialize the bundle generator
    let config_path = Path::new("config/protocols.yaml");
    let generator = BundleGenerator::new(config_path)?;
    
    // Create a cross-chain arbitrage opportunity
    let analysis = AnalysisResult::FullMatch {
        pattern: PatternMatch {
            pattern_type: PatternType::CrossChainArbitrage,
            confidence: 0.85,
        },
        bundle: common::types::Bundle {
            name: "Cross-Chain WETH Arbitrage".to_string(),
            start_chain: common::types::Chain::Polygon,
            constraints: vec![],
            expr: common::types::Expr::Seq {
                first: Box::new(common::types::Expr::Action {
                    action: common::types::Action::Swap {
                        amount_in: common::types::Rational::from_integer(1000000000000000000), // 1 WETH
                        token_in: common::types::Token::WETH,
                        token_out: common::types::Token::USDC,
                        min_out: common::types::Rational::from_integer(1500000000), // 1500 USDC
                        protocol: common::types::Protocol::UniswapV2,
                    },
                }),
                second: Box::new(common::types::Expr::Seq {
                    first: Box::new(common::types::Expr::Action {
                        action: common::types::Action::Bridge {
                            chain: common::types::Chain::Arbitrum,
                            token: common::types::Token::USDC,
                            amount: common::types::Rational::from_integer(1500000000),
                        },
                    }),
                    second: Box::new(common::types::Expr::Action {
                        action: common::types::Action::Swap {
                            amount_in: common::types::Rational::from_integer(1500000000),
                            token_in: common::types::Token::USDC,
                            token_out: common::types::Token::WETH,
                            min_out: common::types::Rational::from_integer(1010000000000000000), // 1.01 WETH
                            protocol: common::types::Protocol::UniswapV2,
                        },
                    }),
                }),
            },
        },
        confidence: 0.85,
    };
    
    // Generate the execution bundle
    let bundle = generator.generate(analysis)?;
    
    // Pretty print the result
    let json = serde_json::to_string_pretty(&bundle)
        .map_err(|e| BundleGeneratorError::EncodingError(e.to_string()))?;
    println!("Generated Cross-Chain Execution Bundle:");
    println!("{}", json);
    
    // Print summary
    println!("\n=== Cross-Chain Summary ===");
    println!("Bundle ID: {}", bundle.bundle_id);
    println!("Pattern: {}", bundle.pattern_id);
    println!("Total Steps: {}", bundle.execution_plan.total_steps);
    println!("Estimated Duration: {} seconds", bundle.execution_plan.estimated_duration);
    
    // Show gas per chain
    println!("\nGas Usage by Chain:");
    for (chain, gas) in &bundle.gas_config.gas_by_chain {
        println!("  {:?}: {} gas units", chain, gas);
    }
    println!("Total Gas: {} gas units", bundle.gas_config.total_gas_estimate);
    
    // Show bridge information
    println!("\nBridge Operations:");
    for step in &bundle.execution_plan.operations {
        if let OperationType::Bridge { bridge_protocol, from_chain, to_chain, token, amount } = &step.operation {
            println!("  {} {} from {:?} to {:?} via {}", 
                amount, 
                format!("{:?}", token),
                from_chain,
                to_chain,
                bridge_protocol
            );
        }
    }
    
    Ok(())
}