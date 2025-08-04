//! Pipeline demonstration showing compiler integration
//!
//! Run with: cargo run --example pipeline_demo

use analyzer::{CompilerInterface, CompilerMessage, AnalyzerEngine};
use analyzer::common::{Bundle, Expr, Action, Chain, Protocol, Token, Rational, Constraint};
use analyzer::integration::compiler_interface::AnalyzerResponse;

fn main() {
    env_logger::init();
    
    println!("🚀 Atomic Mesh Analyzer Pipeline Demonstration\n");
    
    // Create analyzer and interface
    let analyzer = AnalyzerEngine::new().expect("Failed to create analyzer");
    let mut interface = CompilerInterface::new(analyzer);
    
    // Demonstrate different message types
    println!("📡 Simulating compiler messages...\n");
    
    // 1. Status check
    send_and_process(&mut interface, CompilerMessage::StatusRequest);
    
    // 2. Simple swap
    let simple_swap = create_simple_swap();
    send_and_process(&mut interface, CompilerMessage::AnalyzeBundle {
        id: "swap-001".to_string(),
        bundle: simple_swap,
    });
    
    // 3. Flash loan arbitrage
    let flash_loan = create_flash_loan_arb();
    send_and_process(&mut interface, CompilerMessage::AnalyzeBundle {
        id: "flash-001".to_string(),
        bundle: flash_loan,
    });
    
    // 4. Complex multi-protocol bundle
    let complex = create_complex_bundle();
    send_and_process(&mut interface, CompilerMessage::AnalyzeBundle {
        id: "complex-001".to_string(),
        bundle: complex,
    });
    
    // 5. Invalid bundle (for rejection demo)
    let invalid = create_invalid_bundle();
    send_and_process(&mut interface, CompilerMessage::AnalyzeBundle {
        id: "invalid-001".to_string(),
        bundle: invalid,
    });
    
    // 6. Final status check
    println!("\n📊 Final status check:");
    send_and_process(&mut interface, CompilerMessage::StatusRequest);
    
    println!("\n✅ Pipeline demonstration complete!");
}

fn send_and_process(interface: &mut CompilerInterface, message: CompilerMessage) {
    // Simulate sending message
    let msg_json = serde_json::to_string(&message).unwrap();
    println!("➡️  Sending: {}", truncate(&msg_json, 100));
    
    // Process and get response
    let response = interface.process_message(message).unwrap();
    let resp_json = serde_json::to_string(&response).unwrap();
    
    // Pretty print response
    match response {
        AnalyzerResponse::Status { healthy, patterns_loaded, analyses_completed, average_latency_us } => {
            println!("⬅️  Status Response:");
            println!("   - Healthy: {}", healthy);
            println!("   - Patterns Loaded: {}", patterns_loaded);
            println!("   - Analyses Completed: {}", analyses_completed);
            println!("   - Average Latency: {}μs", average_latency_us);
        }
        
        AnalyzerResponse::AnalysisResult { id, result, timing_us } => {
            println!("⬅️  Analysis Result for '{}':", id);
            
            let verdict = match &result {
                analyzer::integration::compiler_interface::AnalysisResultDTO::Valid { .. } => "✅ VALID",
                analyzer::integration::compiler_interface::AnalysisResultDTO::NeedsReview { .. } => "⚠️  NEEDS REVIEW",
                analyzer::integration::compiler_interface::AnalysisResultDTO::Rejected { .. } => "❌ REJECTED",
            };
            
            println!("   - Verdict: {}", verdict);
            println!("   - Analysis Time: {}μs", timing_us);
            
            // Show details based on result type
            match result {
                analyzer::integration::compiler_interface::AnalysisResultDTO::Valid { 
                    confidence, gas_optimization_available, .. 
                } => {
                    println!("   - Confidence: {:.2}", confidence);
                    println!("   - Gas Optimization: {}", if gas_optimization_available { "Available" } else { "Not available" });
                }
                
                analyzer::integration::compiler_interface::AnalysisResultDTO::NeedsReview { 
                    confidence, concerns, .. 
                } => {
                    println!("   - Confidence: {:.2}", confidence);
                    println!("   - Concerns: {} items", concerns.len());
                }
                
                analyzer::integration::compiler_interface::AnalysisResultDTO::Rejected { 
                    reason, .. 
                } => {
                    println!("   - Reason: {}", reason);
                }
            }
        }
        
        _ => {
            println!("⬅️  Response: {}", truncate(&resp_json, 100));
        }
    }
    
    println!();
}

fn truncate(s: &str, max_len: usize) -> String {
    if s.len() <= max_len {
        s.to_string()
    } else {
        format!("{}...", &s[..max_len])
    }
}

// Bundle creation helpers
fn create_simple_swap() -> Bundle {
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

fn create_flash_loan_arb() -> Bundle {
    Bundle {
        name: "flash_loan_arbitrage".to_string(),
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
                        amount_in: Rational::from_integer(10000),
                        min_out: Rational::from_integer(15000),
                    }
                }),
                second: Box::new(Expr::Seq {
                    first: Box::new(Expr::Action {
                        action: Action::Swap {
                            protocol: Protocol::UniswapV2,
                            token_in: Token::USDC,
                            token_out: Token::WETH,
                            amount_in: Rational::from_integer(15000),
                            min_out: Rational::from_integer(10100),
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
        },
        constraints: vec![
            Constraint::Deadline { blocks: 1 },
        ],
    }
}

fn create_complex_bundle() -> Bundle {
    Bundle {
        name: "complex_multi_protocol".to_string(),
        start_chain: Chain::Polygon,
        expr: Expr::Seq {
            first: Box::new(Expr::Action {
                action: Action::Borrow {
                    protocol: Protocol::Compound,
                    amount: Rational::from_integer(5000),
                    token: Token::USDC,
                }
            }),
            second: Box::new(Expr::Seq {
                first: Box::new(Expr::Action {
                    action: Action::Swap {
                        protocol: Protocol::UniswapV2,
                        token_in: Token::USDC,
                        token_out: Token::WETH,
                        amount_in: Rational::from_integer(5000),
                        min_out: Rational::from_integer(10),
                    }
                }),
                second: Box::new(Expr::Seq {
                    first: Box::new(Expr::Action {
                        action: Action::Swap {
                            protocol: Protocol::UniswapV2,
                            token_in: Token::WETH,
                            token_out: Token::USDC,
                            amount_in: Rational::from_integer(10),
                            min_out: Rational::from_integer(5050),
                        }
                    }),
                    second: Box::new(Expr::Action {
                        action: Action::Repay {
                            protocol: Protocol::Compound,
                            amount: Rational::from_integer(5000),
                            token: Token::USDC,
                        }
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

fn create_invalid_bundle() -> Bundle {
    Bundle {
        name: "invalid_bundle".to_string(),
        start_chain: Chain::Polygon,
        expr: Expr::Action {
            action: Action::Swap {
                protocol: Protocol::UniswapV2,
                token_in: Token::WETH,
                token_out: Token::USDC,
                amount_in: Rational::from_integer(100),
                min_out: Rational::from_integer(0), // Invalid: zero min_out
            }
        },
        constraints: vec![
            Constraint::Deadline { blocks: 0 }, // Invalid: zero deadline
        ],
    }
}