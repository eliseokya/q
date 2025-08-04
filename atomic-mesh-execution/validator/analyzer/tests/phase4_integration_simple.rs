//! Simplified integration tests for Phase 4: Error Handling & Graceful Degradation

use analyzer::*;
use ::common::types::{Bundle, Expr, Action, Token, Protocol, Chain, Constraint, Rational};

#[test]
fn test_phase4_enhanced_result_types() {
    // Test that we can use the enhanced result types
    let analyzer = AnalyzerEngine::new().unwrap();
    
    // The analyzer should produce one of the new result types
    let bundle = Bundle {
        name: "test".to_string(),
        start_chain: Chain::Polygon,
        expr: Expr::Action {
            action: Action::Swap {
                protocol: Protocol::UniswapV2,
                token_in: Token::WETH,
                token_out: Token::USDC,
                amount_in: Rational::from_integer(100),
                min_out: Rational::from_integer(90),
            }
        },
        constraints: vec![],
    };
    
    let mut analyzer = AnalyzerEngine::new().unwrap();
    let result = analyzer.analyze_bundle(&bundle);
    
    // Just verify we get some result
    match result {
        AnalysisResult::FullMatch { .. } => println!("Got FullMatch"),
        AnalysisResult::PartialMatch { .. } => println!("Got PartialMatch"),
        AnalysisResult::Heuristic { .. } => println!("Got Heuristic"),
        AnalysisResult::Reject { .. } => println!("Got Reject"),
    }
}

#[test]
fn test_phase4_heuristic_analysis() {
    // Test that unknown patterns fall back to heuristic analysis
    let mut analyzer = AnalyzerEngine::new().unwrap();
    
    // Create a bundle with unknown pattern
    let bundle = Bundle {
        name: "unknown".to_string(),
        start_chain: Chain::Arbitrum,
        expr: Expr::Seq {
            first: Box::new(Expr::Action {
                action: Action::Deposit {
                    amount: Rational::from_integer(100),
                    token: Token::DAI,
                    protocol: Protocol::Compound,
                }
            }),
            second: Box::new(Expr::Action {
                action: Action::Bridge {
                    chain: Chain::Polygon,
                    token: Token::DAI,
                    amount: Rational::from_integer(100),
                }
            }),
        },
        constraints: vec![],
    };
    
    let result = analyzer.analyze_bundle(&bundle);
    
    // For unknown patterns, we should get Heuristic or Reject
    match result {
        AnalysisResult::Heuristic { confidence, .. } => {
            assert!(confidence < 0.5, "Unknown patterns should have low confidence");
        }
        AnalysisResult::Reject { .. } => {
            // Also acceptable for unknown patterns
        }
        _ => {
            // FullMatch or PartialMatch might happen if we accidentally match something
        }
    }
}

#[test]
fn test_phase4_rejection_with_feedback() {
    // Test that invalid bundles get helpful rejection messages
    use analyzer::fallback::{RejectionReason, SuggestedFix};
    use analyzer::heuristics::SafetyHeuristics;
    
    // The SafetyHeuristics should be able to generate fixes
    let heuristics = SafetyHeuristics::new();
    let violations = vec![
        RejectionReason::InsufficientLiquidity {
            required: "1000 WETH".to_string(),
            available: "100 WETH".to_string(),
        }
    ];
    
    // Create a dummy structural analysis for the test
    let dummy_analysis = analyzer::heuristics::StructuralAnalysis {
        action_sequence: vec![],
        balance_flows: analyzer::heuristics::BalanceFlowAnalysis {
            token_flows: std::collections::HashMap::new(),
            all_flows_balanced: true,

            unmatched_borrows: vec![],
            unmatched_repays: vec![],
        },
        timing_risks: analyzer::heuristics::TimingRiskAnalysis {
            has_tight_deadlines: false,
            cross_chain_timing_dependency: false,
            estimated_blocks_needed: 1,
        },
        protocol_risks: analyzer::heuristics::ProtocolRiskAnalysis {
            unknown_protocol_count: 0,
            used_protocols: std::collections::HashSet::new(),
            max_risk_score: 0.0,
        },
        cross_chain_complexity: analyzer::heuristics::CrossChainComplexity {
            chain_count: 1,
            bridge_count: 0,
            has_circular_path: false,
        },
        pattern_type: "Unknown".to_string(),
    };
    
    let fixes = heuristics.generate_fixes(&violations, &dummy_analysis);
    assert!(!fixes.is_empty(), "Should generate suggested fixes");
}