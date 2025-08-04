//! Performance demonstration for the Analyzer
//! 
//! Run with: cargo run --example performance_demo --release

use analyzer::{AnalyzerEngine, PerformanceBudget};
use analyzer::common::{Bundle, Expr, Action, Chain, Protocol, Token, Constraint, Rational};
use std::time::Instant;

fn main() {
    env_logger::init();
    
    println!("🚀 Analyzer Performance Demonstration\n");
    
    let mut analyzer = AnalyzerEngine::new().expect("Failed to create analyzer");
    
    // Set production performance budget
    analyzer.set_performance_budget(PerformanceBudget::strict_budget());
    
    println!("📊 Running performance tests...\n");
    
    // Test 1: Simple swap
    let simple_bundle = create_simple_bundle();
    benchmark_bundle(&mut analyzer, &simple_bundle, "Simple Swap");
    
    // Test 2: Flash loan arbitrage
    let flash_loan_bundle = create_flash_loan_bundle();
    benchmark_bundle(&mut analyzer, &flash_loan_bundle, "Flash Loan Arbitrage");
    
    // Test 3: Complex multi-hop
    let complex_bundle = create_complex_bundle();
    benchmark_bundle(&mut analyzer, &complex_bundle, "Complex Multi-Hop");
    
    // Print overall metrics
    println!("\n📈 Overall Performance Metrics:");
    println!("{}", analyzer.get_metrics_report());
}

fn benchmark_bundle(analyzer: &mut AnalyzerEngine, bundle: &Bundle, name: &str) {
    println!("Testing: {}", name);
    println!("{}", "-".repeat(50));
    
    // Warm up
    for _ in 0..5 {
        let _ = analyzer.analyze_bundle(bundle);
    }
    
    // Actual benchmark
    let iterations = 100;
    let start = Instant::now();
    
    for _ in 0..iterations {
        let _ = analyzer.analyze_bundle(bundle);
    }
    
    let total_duration = start.elapsed();
    let avg_duration = total_duration / iterations;
    
    println!("Average time: {}μs", avg_duration.as_micros());
    println!("Throughput: {} bundles/second", 1_000_000 / avg_duration.as_micros());
    
    // Get last timing breakdown
    let timing_report = analyzer.get_timing_report();
    println!("\nDetailed breakdown (last run):");
    println!("{}\n", timing_report);
}

fn create_simple_bundle() -> Bundle {
    Bundle {
        name: "simple_swap".to_string(),
        start_chain: Chain::Polygon,
        expr: Expr::Action {
            action: Action::Swap {
                protocol: Protocol::UniswapV2,
                token_in: Token::WETH,
                token_out: Token::USDC,
                amount_in: Rational::from_integer(100),
                min_out: Rational::from_integer(150),
            }
        },
        constraints: vec![],
    }
}

fn create_flash_loan_bundle() -> Bundle {
    Bundle {
        name: "flash_loan_arb".to_string(),
        start_chain: Chain::Polygon,
        expr: Expr::Seq {
            first: Box::new(Expr::Action {
                action: Action::Borrow {
                    protocol: Protocol::Aave,
                    amount: Rational::from_integer(1000),
                    token: Token::WETH,
                }
            }),
            second: Box::new(Expr::Seq {
                first: Box::new(Expr::Action {
                    action: Action::Swap {
                        protocol: Protocol::UniswapV2,
                        token_in: Token::WETH,
                        token_out: Token::USDC,
                        amount_in: Rational::from_integer(1000),
                        min_out: Rational::from_integer(1500),
                    }
                }),
                second: Box::new(Expr::Action {
                    action: Action::Repay {
                        protocol: Protocol::Aave,
                        amount: Rational::from_integer(1000),
                        token: Token::WETH,
                    }
                }),
            }),
        },
        constraints: vec![
            Constraint::Deadline { blocks: 1 },
        ],
    }
}

fn create_complex_bundle() -> Bundle {
    Bundle {
        name: "complex_multi_hop".to_string(),
        start_chain: Chain::Polygon,
        expr: Expr::Seq {
            first: Box::new(Expr::Action {
                action: Action::Borrow {
                    protocol: Protocol::Aave,
                    amount: Rational::from_integer(10000),
                    token: Token::WETH,
                }
            }),
            second: Box::new(Expr::Seq {
                first: Box::new(Expr::Action {
                    action: Action::Swap {
                        protocol: Protocol::UniswapV2,
                        token_in: Token::WETH,
                        token_out: Token::USDC,
                        amount_in: Rational::from_integer(5000),
                        min_out: Rational::from_integer(7500),
                    }
                }),
                second: Box::new(Expr::Seq {
                    first: Box::new(Expr::Action {
                        action: Action::Swap {
                            protocol: Protocol::UniswapV2,
                            token_in: Token::USDC,
                            token_out: Token::WETH,
                            amount_in: Rational::from_integer(7500),
                            min_out: Rational::from_integer(5100),
                        }
                    }),
                    second: Box::new(Expr::Seq {
                        first: Box::new(Expr::Action {
                            action: Action::Swap {
                                protocol: Protocol::UniswapV2,
                                token_in: Token::WETH,
                                token_out: Token::USDC,
                                amount_in: Rational::from_integer(5000),
                                min_out: Rational::from_integer(7500),
                            }
                        }),
                        second: Box::new(Expr::Action {
                            action: Action::Repay {
                                protocol: Protocol::Aave,
                                amount: Rational::from_integer(10000),
                                token: Token::WETH,
                            }
                        }),
                    }),
                }),
            }),
        },
        constraints: vec![
            Constraint::Deadline { blocks: 5 },
            Constraint::MaxGas { amount: 1000000 },
        ],
    }
}