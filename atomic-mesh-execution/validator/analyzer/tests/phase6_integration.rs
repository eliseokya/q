//! Phase 6 Integration Tests - Compiler Integration & Pipeline

use analyzer::{
    CompilerInterface, CompilerMessage, AnalyzerEngine,
    PipelineBuilder, PipelineConfig
};
use analyzer::common::{Bundle, Expr, Action, Chain, Protocol, Token, Rational};
use serde_json;

#[test]
fn test_compiler_message_parsing() {
    // Test analyze bundle message
    let bundle = Bundle {
        name: "test_bundle".to_string(),
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
    };
    
    let message = CompilerMessage::AnalyzeBundle {
        id: "test-123".to_string(),
        bundle: bundle.clone(),
    };
    
    let json = serde_json::to_string(&message).unwrap();
    println!("Serialized message: {}", json);
    
    // Verify it can be parsed back
    let parsed: CompilerMessage = serde_json::from_str(&json).unwrap();
    match parsed {
        CompilerMessage::AnalyzeBundle { id, bundle: parsed_bundle } => {
            assert_eq!(id, "test-123");
            assert_eq!(parsed_bundle.name, bundle.name);
        }
        _ => panic!("Wrong message type"),
    }
}

#[test]
fn test_status_request_message() {
    let message = CompilerMessage::StatusRequest;
    let json = serde_json::to_string(&message).unwrap();
    assert!(json.contains("status_request"));
    
    let parsed: CompilerMessage = serde_json::from_str(&json).unwrap();
    assert!(matches!(parsed, CompilerMessage::StatusRequest));
}

#[test]
fn test_compiler_interface_response() {
    let analyzer = AnalyzerEngine::new().expect("Failed to create analyzer");
    let mut interface = CompilerInterface::new(analyzer);
    
    // Create a test bundle
    let bundle = Bundle {
        name: "interface_test".to_string(),
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
    };
    
    let message = CompilerMessage::AnalyzeBundle {
        id: "resp-test".to_string(),
        bundle,
    };
    
    // Process the message
    let response = interface.process_message(message).unwrap();
    
    // Verify response structure
    match response {
        analyzer::integration::compiler_interface::AnalyzerResponse::AnalysisResult { id, result, timing_us } => {
            assert_eq!(id, "resp-test");
            assert!(timing_us > 0);
            
            // Check the result is properly formatted
            let json = serde_json::to_string(&result).unwrap();
            println!("Analysis result: {}", json);
            assert!(json.contains("verdict"));
        }
        _ => panic!("Wrong response type"),
    }
}

#[test]
fn test_pipeline_configuration() {
    // Test default configuration
    let config = PipelineConfig::default();
    assert_eq!(config.performance_mode, "production");
    assert!(!config.verbose);
    assert_eq!(config.max_bundles, 0);
    assert_eq!(config.metrics_interval, 1000);
    
    // Test JSON serialization
    let json = serde_json::to_string(&config).unwrap();
    let parsed: PipelineConfig = serde_json::from_str(&json).unwrap();
    assert_eq!(parsed.performance_mode, config.performance_mode);
}

#[test]
fn test_pipeline_builder() {
    // Test building with different modes
    let pipeline = PipelineBuilder::new()
        .performance_mode("development")
        .verbose(true)
        .build();
    
    assert!(pipeline.is_ok());
    
    // Test invalid mode
    let invalid = PipelineBuilder::new()
        .performance_mode("invalid_mode")
        .build();
    
    assert!(invalid.is_err());
    let err_msg = invalid.err().unwrap().to_string();
    assert!(err_msg.contains("Invalid performance mode"));
}

#[test]
fn test_end_to_end_message_flow() {
    // This test simulates a complete message flow
    let analyzer = AnalyzerEngine::new().expect("Failed to create analyzer");
    let mut interface = CompilerInterface::new(analyzer);
    
    // Test sequence of messages
    let messages = vec![
        // First, check status
        CompilerMessage::StatusRequest,
        
        // Analyze a simple swap
        CompilerMessage::AnalyzeBundle {
            id: "swap-1".to_string(),
            bundle: create_test_bundle("simple_swap"),
        },
        
        // Analyze a flash loan
        CompilerMessage::AnalyzeBundle {
            id: "flash-1".to_string(),
            bundle: create_flash_loan_bundle(),
        },
        
        // Check status again
        CompilerMessage::StatusRequest,
    ];
    
    for message in messages {
        let response = interface.process_message(message).unwrap();
        
        match response {
            analyzer::integration::compiler_interface::AnalyzerResponse::Status { healthy, patterns_loaded, analyses_completed, .. } => {
                assert!(healthy);
                assert!(patterns_loaded > 0);
                println!("Status: {} analyses completed", analyses_completed);
            }
            analyzer::integration::compiler_interface::AnalyzerResponse::AnalysisResult { id, result, timing_us } => {
                println!("Analysis {} completed in {}μs", id, timing_us);
                
                // Verify the result has the expected structure
                let json = serde_json::to_string(&result).unwrap();
                assert!(json.contains("verdict"));
            }
            _ => {}
        }
    }
}

#[test]
fn test_shutdown_handling() {
    let analyzer = AnalyzerEngine::new().expect("Failed to create analyzer");
    let mut interface = CompilerInterface::new(analyzer);
    
    let response = interface.process_message(CompilerMessage::Shutdown).unwrap();
    
    match response {
        analyzer::integration::compiler_interface::AnalyzerResponse::ShutdownAck => {
            // Success
        }
        _ => panic!("Expected shutdown acknowledgment"),
    }
}

// Helper functions
fn create_test_bundle(name: &str) -> Bundle {
    Bundle {
        name: name.to_string(),
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
        name: "flash_loan_test".to_string(),
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
        constraints: vec![],
    }
}