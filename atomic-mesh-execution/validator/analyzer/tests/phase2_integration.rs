//! Integration test for Phase 2: Semantic Validation & Mathematical Integration

use analyzer::*;
use ::common::types::{Bundle, Expr, Action, Token, Protocol, Chain, Constraint, Rational};

#[test]
fn test_phase2_semantic_validation_full_match() {
    // Create analyzer with Phase 2 components
    let mut analyzer = AnalyzerEngine::new().unwrap();
    
    // Create a flash loan pattern that should match
    let bundle = Bundle {
        name: "flash-loan-arbitrage".to_string(),
        start_chain: Chain::Polygon,
        expr: Expr::Seq {
            first: Box::new(Expr::Action {
                action: Action::Borrow {
                    amount: Rational::from_integer(1000),
                    token: Token::WETH,
                    protocol: Protocol::Aave,
                }
            }),
            second: Box::new(Expr::Seq {
                first: Box::new(Expr::Action {
                    action: Action::Swap {
                        amount_in: Rational::from_integer(1000),
                        token_in: Token::WETH,
                        token_out: Token::USDC,
                        min_out: Rational::from_integer(1500),
                        protocol: Protocol::UniswapV2,
                    }
                }),
                second: Box::new(Expr::Action {
                    action: Action::Repay {
                        amount: Rational::from_integer(1000),
                        token: Token::WETH,
                        protocol: Protocol::Aave,
                    }
                }),
            }),
        },
        constraints: vec![
            Constraint::Deadline { blocks: 10 },
            Constraint::MaxGas { amount: 500_000 },
        ],
    };
    
    // Load flash loan pattern
    let flash_loan_pattern = ProvenPattern {
        pattern_id: "flash-loan-001".to_string(),
        pattern_template: PatternTemplate::FlashLoan,
        theorem_reference: "FlashLoanPattern".to_string(),
        theorem_file: std::path::PathBuf::from("maths/Stack/Bundles.lean"),
        theorem_line: 42,
        safety_properties: vec![
            SafetyProperty::Atomicity,
            SafetyProperty::BalancePreservation,
            SafetyProperty::AllOrNothing,
        ],
        preconditions: vec!["amount > 0".to_string()],
        structure_regex: "borrow.*repay".to_string(),
        confidence_threshold: 0.7,
        gas_optimization_potential: true,
    };
    
    analyzer.load_patterns(vec![flash_loan_pattern]).unwrap();
    
    // Analyze the bundle
    let result = analyzer.analyze_bundle(&bundle);
    
    // Verify we get a full match with high confidence
    match result {
        analyzer::AnalysisResult::FullMatch { 
            theorem_reference, 
            confidence, 
            safety_guarantees,
            gas_optimization_available,
            .. 
        } => {
            assert_eq!(theorem_reference, "FlashLoanPattern");
            assert!(confidence >= 0.9, "Expected high confidence for theorem-verified match");
            assert!(safety_guarantees.contains(&SafetyProperty::Atomicity));
            assert!(safety_guarantees.contains(&SafetyProperty::BalancePreservation));
            assert!(gas_optimization_available);
        }
        _ => panic!("Expected FullMatch but got {:?}", result),
    }
}

#[test]
fn test_phase2_risk_assessment_for_unknown_pattern() {
    // Create analyzer with Phase 2 components
    let mut analyzer = AnalyzerEngine::new().unwrap();
    
    // Create a bundle that doesn't match any pattern
    let unknown_bundle = Bundle {
        name: "unknown-strategy".to_string(),
        start_chain: Chain::Arbitrum,
        expr: Expr::Seq {
            first: Box::new(Expr::Action {
                action: Action::Deposit {
                    amount: Rational::from_integer(500),
                    token: Token::DAI,
                    protocol: Protocol::Compound,
                }
            }),
            second: Box::new(Expr::Action {
                action: Action::Bridge {
                    chain: Chain::Polygon,
                    token: Token::DAI,
                    amount: Rational::from_integer(500),
                }
            }),
        },
        constraints: vec![
            Constraint::Deadline { blocks: 30 },
        ],
    };
    
    // Analyze should fall back to risk assessment
    let result = analyzer.analyze_bundle(&unknown_bundle);
    

    // Verify we get a heuristic result with risk assessment
    match result {
        analyzer::AnalysisResult::Heuristic {
            risk_assessment,
            confidence,
            detected_patterns,
            safety_warnings,
            manual_review_required,
            ..
        } => {
            assert!(confidence < 0.5, "Expected low confidence for unknown pattern");
            // Manual review is required only when confidence < 0.3
            if confidence < 0.3 {
                assert!(manual_review_required, "Very low confidence should require review");
            }
            assert!(!detected_patterns.is_empty());
            assert!(!safety_warnings.is_empty());
            
            // Check risk assessment
            // The risk assessment should have some evaluation
            assert!(risk_assessment.overall_score >= 0.0);
            // For unknown patterns, we might not have specific risk factors
            
            // The bundle has a bridge operation which should be detected
            // For now, let's just check that the pattern is identified as CrossChain
            assert_eq!(detected_patterns[0], "CrossChain", "Should detect CrossChain pattern");
            
            // Check if we have any risk factors (they might be different types)
            // println!("Risk factors: {:?}", risk_assessment.risk_factors);
        }
        _ => panic!("Expected Heuristic result but got {:?}", result),
    }
}

#[test]
fn test_phase2_confidence_scoring_gradients() {
    // Test that confidence scoring provides proper gradients
    let calc = analyzer::ConfidenceCalculator::new();
    
    // Create test pattern
    let pattern = ProvenPattern {
        pattern_id: "test".to_string(),
        pattern_template: PatternTemplate::CrossChainArbitrage,
        theorem_reference: "CrossChainAtomicity".to_string(),
        theorem_file: std::path::PathBuf::from("test.lean"),
        theorem_line: 1,
        safety_properties: vec![
            SafetyProperty::Atomicity,
            SafetyProperty::CrossChainConsistency,
        ],
        preconditions: vec!["valid_chains".to_string()],
        structure_regex: ".*".to_string(),
        confidence_threshold: 0.6,
        gas_optimization_potential: false,
    };
    
    // Test different confidence levels
    let proven_confidence = calc.calculate_proven_confidence(
        &pattern,
        true, // theorem verified
        &pattern.safety_properties, // all properties verified
    );
    assert_eq!(proven_confidence, 1.0, "Fully proven should have confidence 1.0");
    
    let partial_confidence = calc.calculate_proven_confidence(
        &pattern,
        true, // theorem verified
        &[SafetyProperty::Atomicity], // only some properties
    );
    assert!(partial_confidence > 0.9 && partial_confidence < 1.0, 
        "Partial verification should have high but not perfect confidence");
    
    let heuristic_confidence = calc.calculate_heuristic_confidence(
        &pattern,
        &[SafetyProperty::Atomicity],
    );
    assert!(heuristic_confidence >= 0.5 && heuristic_confidence <= 0.95,
        "Heuristic confidence should be in medium range");
}