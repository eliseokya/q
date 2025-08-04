//! Phase 5 Performance Tests - Performance Monitoring & Production Readiness

use analyzer::{
    AnalyzerEngine, 
    PerformanceBudget, HealthChecker, HealthStatus
};
use analyzer::common::{AnalysisResult, Bundle, Expr, Action, Chain, Protocol, Token, Constraint, Rational};

#[test]
fn test_performance_monitoring() {
    let _ = env_logger::try_init();
    
    let mut analyzer = AnalyzerEngine::new().expect("Failed to create analyzer");
    
    // Create a test bundle
    let bundle = Bundle {
        name: "performance_test".to_string(),
        start_chain: Chain::Polygon,
        expr: Expr::Seq {
            first: Box::new(Expr::Action {
                action: Action::Borrow {
                    protocol: Protocol::Aave,
                    amount: Rational::from_integer(100),
                    token: Token::WETH,
                }
            }),
            second: Box::new(Expr::Action {
                action: Action::Swap {
                    protocol: Protocol::UniswapV2,
                    token_in: Token::WETH,
                    token_out: Token::USDC,
                    amount_in: Rational::from_integer(100),
                    min_out: Rational::from_integer(150),
                }
            }),
        },
        constraints: vec![
            Constraint::Deadline { blocks: 10 },
        ],
    };
    
    // Analyze the bundle
    let result = analyzer.analyze_bundle(&bundle);
    
    // Get timing report
    let timing_report = analyzer.get_timing_report();
    println!("\n{}", timing_report);
    
    // Verify we got a result
    match result {
        AnalysisResult::FullMatch { .. } => println!("Got full match"),
        AnalysisResult::PartialMatch { .. } => println!("Got partial match"),
        AnalysisResult::Heuristic { .. } => println!("Got heuristic result"),
        AnalysisResult::Reject { .. } => println!("Got rejection"),
    }
    
    // Check that timing was recorded
    assert!(timing_report.contains("Total Duration:"));
    assert!(timing_report.contains("Input Parsing:"));
    assert!(timing_report.contains("Pattern Loading:"));
    assert!(timing_report.contains("Structural Matching:"));
}

#[test]
fn test_metrics_collection() {
    let mut analyzer = AnalyzerEngine::new().expect("Failed to create analyzer");
    
    // Run multiple analyses to collect metrics
    for i in 0..10 {
        let bundle = Bundle {
            name: format!("metrics_test_{}", i),
            start_chain: Chain::Polygon,
            expr: Expr::Action {
                action: Action::Swap {
                    protocol: Protocol::UniswapV2,
                    token_in: Token::WETH,
                    token_out: Token::USDC,
                    amount_in: Rational::from_integer((i + 1) as u64),
                    min_out: Rational::from_integer((i + 1) as u64),
                }
            },
            constraints: vec![],
        };
        
        let _ = analyzer.analyze_bundle(&bundle);
    }
    
    // Get metrics report
    let metrics_report = analyzer.get_metrics_report();
    println!("\n{}", metrics_report);
    
    // Verify metrics were collected
    assert!(metrics_report.contains("Total Analyses: 10"));
    assert!(metrics_report.contains("Performance"));
    assert!(metrics_report.contains("P50:"));
    assert!(metrics_report.contains("P95:"));
}

#[test]
fn test_performance_budgets() {
    let mut analyzer = AnalyzerEngine::new().expect("Failed to create analyzer");
    
    // Set development budget (more lenient)
    analyzer.set_performance_budget(PerformanceBudget::development_budget());
    
    let bundle = Bundle {
        name: "budget_test".to_string(),
        start_chain: Chain::Polygon,
        expr: Expr::Action {
            action: Action::Swap {
                protocol: Protocol::UniswapV2,
                token_in: Token::WETH,
                token_out: Token::USDC,
                amount_in: Rational::from_integer(100),
                min_out: Rational::from_integer(100),
            }
        },
        constraints: vec![],
    };
    
    let _ = analyzer.analyze_bundle(&bundle);
    let timing_report = analyzer.get_timing_report();
    
    // Development budget should be 2ms (2000μs)
    println!("\nDevelopment Budget Test:\n{}", timing_report);
    
    // Now set strict production budget
    analyzer.set_performance_budget(PerformanceBudget::strict_budget());
    
    let _ = analyzer.analyze_bundle(&bundle);
    let timing_report = analyzer.get_timing_report();
    
    // Strict budget should be 300μs
    println!("\nStrict Budget Test:\n{}", timing_report);
}

#[test]
fn test_health_checks() {
    let mut analyzer = AnalyzerEngine::new().expect("Failed to create analyzer");
    
    // Basic health check
    let health_checker = HealthChecker::new();
    let health_status = health_checker.check_health(&mut analyzer);
    
    match &health_status {
        HealthStatus::Healthy { message, latency_ms } => {
            println!("✅ System is healthy: {}", message);
            println!("Health check latency: {}ms", latency_ms);
        },
        HealthStatus::Degraded { message, issues } => {
            println!("⚠️ System is degraded: {}", message);
            println!("Issues: {:?}", issues);
        },
        HealthStatus::Unhealthy { message, errors } => {
            println!("❌ System is unhealthy: {}", message);
            println!("Errors: {:?}", errors);
        }
    }
    
    // Get health report
    let report = health_checker.get_health_report(&health_status);
    println!("\n{}", report);
    
    // System should be healthy with patterns loaded
    match health_status {
        HealthStatus::Healthy { .. } => {},
        HealthStatus::Degraded { .. } => {
            // Degraded is acceptable if we have some patterns
            assert!(analyzer.get_pattern_count() > 0);
        },
        HealthStatus::Unhealthy { .. } => panic!("System should not be unhealthy"),
    }
}

#[test]
fn test_real_world_performance() {
    let mut analyzer = AnalyzerEngine::new().expect("Failed to create analyzer");
    
    // Complex real-world bundle
    let bundle = Bundle {
        name: "complex_arbitrage".to_string(),
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
                        amount_in: Rational::from_integer(500),
                        min_out: Rational::from_integer(750),
                    }
                }),
                second: Box::new(Expr::Seq {
                    first: Box::new(Expr::Action {
                        action: Action::Swap {
                            protocol: Protocol::UniswapV2,
                            token_in: Token::USDC,
                            token_out: Token::WETH,
                            amount_in: Rational::from_integer(750),
                            min_out: Rational::from_integer(510),
                        }
                    }),
                    second: Box::new(Expr::Action {
                        action: Action::Swap {
                            protocol: Protocol::UniswapV2,
                            token_in: Token::WETH,
                            token_out: Token::USDC,
                            amount_in: Rational::from_integer(500),
                            min_out: Rational::from_integer(510),
                        }
                    }),
                }),
            }),
        },
        constraints: vec![
            Constraint::Deadline { blocks: 5 },
            Constraint::MaxGas { amount: 500000 },
        ],
    };
    
    // Time the analysis
    let start = std::time::Instant::now();
    let result = analyzer.analyze_bundle(&bundle);
    let duration = start.elapsed();
    
    println!("\nComplex bundle analysis took: {}μs", duration.as_micros());
    
    // Get detailed timing
    let timing_report = analyzer.get_timing_report();
    println!("\n{}", timing_report);
    
    // Verify we got a result quickly
    match result {
        AnalysisResult::FullMatch { .. } => println!("✅ Full match found"),
        AnalysisResult::PartialMatch { .. } => println!("⚠️ Partial match found"),
        AnalysisResult::Heuristic { .. } => println!("🔍 Heuristic analysis performed"),
        AnalysisResult::Reject { .. } => println!("❌ Bundle rejected"),
    }
    
    // Should complete within 2ms even for complex bundles
    assert!(duration.as_millis() < 2, "Analysis took too long: {}ms", duration.as_millis());
}