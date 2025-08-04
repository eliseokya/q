//! Simple integration tests for Phase 4: Error Handling & Graceful Degradation

use analyzer::*;
use ::common::types::{Bundle, Expr, Action, Token, Protocol, Chain, Constraint, Rational};

#[test]
fn test_analyzer_builds_and_runs() {
    // Simple test to verify the analyzer can be created
    let mut analyzer = AnalyzerEngine::new().unwrap();
    
    // Create a simple bundle
    let bundle = Bundle {
        name: "test-bundle".to_string(),
        start_chain: Chain::Polygon,
        expr: Expr::Action {
            action: Action::Swap {
                protocol: Protocol::UniswapV2,
                token_in: Token::WETH,
                token_out: Token::USDC,
                amount_in: Rational { num: 1000, den: 1 },
                min_out: Rational { num: 900, den: 1 },
            }
        },
        constraints: vec![],
    };
    
    // Analyze the bundle
    let result = analyzer.analyze_bundle(&bundle);
    
    // The result should be some kind of analysis result (don't check specifics)
    match result {
        analyzer::AnalysisResult::FullMatch { .. } => {
            // Success - full match
        }
        analyzer::AnalysisResult::PartialMatch { .. } => {
            // Success - partial match
        }
        analyzer::AnalysisResult::Heuristic { .. } => {
            // Success - heuristic analysis
        }
        analyzer::AnalysisResult::Reject { .. } => {
            // Also valid - the analyzer rejected the bundle
        }
    }
}

#[test]
fn test_fallback_types_exist() {
    // Just verify our new types exist and can be created
    use analyzer::fallback::{RiskLevel, FixType, RejectionReason};
    
    let _ = RiskLevel::Low;
    let _ = FixType::AdjustAmount;
    let _ = RejectionReason::MalformedStructure {
        details: "test".to_string()
    };
}

#[test]
fn test_heuristics_types_exist() {
    // Verify heuristic types exist
    use analyzer::heuristics::{StructuralAnalyzer, SafetyHeuristics};
    
    let _ = StructuralAnalyzer::new();
    let _ = SafetyHeuristics::new();
}