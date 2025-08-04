//! Simple example demonstrating bundle generation

use bundle_generator::*;
use std::path::Path;

fn main() -> Result<()> {
    // Initialize the bundle generator
    let config_path = Path::new("config/protocols.yaml");
    let generator = BundleGenerator::new(config_path)?;
    
    // Create a sample analysis result
    let analysis = AnalysisResult::FullMatch {
        pattern: PatternMatch {
            pattern_type: PatternType::FlashLoanArbitrage,
            confidence: 0.95,
        },
        bundle: common::types::Bundle {
            name: "Flash Loan Arbitrage".to_string(),
            start_chain: common::types::Chain::Polygon,
            constraints: vec![],
            expr: common::types::Expr::Seq {
                first: Box::new(common::types::Expr::Action {
                    action: common::types::Action::Borrow {
                        amount: common::types::Rational::from_integer(1000000000000000000), // 1 WETH
                        token: common::types::Token::WETH,
                        protocol: common::types::Protocol::Aave,
                    },
                }),
                second: Box::new(common::types::Expr::Action {
                    action: common::types::Action::Swap {
                        amount_in: common::types::Rational::from_integer(1000000000000000000),
                        token_in: common::types::Token::WETH,
                        token_out: common::types::Token::USDC,
                        min_out: common::types::Rational::from_integer(1500000000), // 1500 USDC
                        protocol: common::types::Protocol::UniswapV2,
                    },
                }),
            },
        },
        confidence: 0.95,
    };
    
    // Generate the execution bundle
    let bundle = generator.generate(analysis)?;
    
    // Pretty print the result
    let json = serde_json::to_string_pretty(&bundle)
        .map_err(|e| BundleGeneratorError::EncodingError(e.to_string()))?;
    println!("Generated Execution Bundle:");
    println!("{}", json);
    
    // Print summary
    println!("\n=== Summary ===");
    println!("Bundle ID: {}", bundle.bundle_id);
    println!("Pattern: {}", bundle.pattern_id);
    println!("Total Steps: {}", bundle.execution_plan.total_steps);
    println!("Total Gas: {} gas units", bundle.gas_config.total_gas_estimate);
    println!("Gas Optimization Potential: {:.1}%", bundle.optimization_hints.gas_optimization_potential * 100.0);
    
    Ok(())
}