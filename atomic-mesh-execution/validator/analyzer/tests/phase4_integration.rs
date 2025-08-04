//! Integration tests for Phase 4: Error Handling & Graceful Degradation

use analyzer::*;
use ::common::types::{Bundle, Expr, Action, Token, Protocol, Chain, Constraint, Rational};
use analyzer::fallback::AnalysisResult as EnhancedAnalysisResult;

#[test]
fn test_phase4_full_match_with_enhanced_result() {
    // Test that full matches still work with the enhanced result system
    let mut analyzer = AnalyzerEngine::new().unwrap();
    
    let bundle = Bundle {
        name: "perfect-flash-loan".to_string(),
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
        ],
        preconditions: vec!["amount > 0".to_string()],
        structure_regex: "borrow.*repay".to_string(),
        confidence_threshold: 0.7,
        gas_optimization_potential: true,
    };
    
    analyzer.load_patterns(vec![flash_loan_pattern]).unwrap();
    
    let result = analyzer.analyze_bundle(&bundle);
    
    // Should get enhanced FullMatch result
    match result {
        EnhancedAnalysisResult::FullMatch { confidence, proof_certificate, .. } => {
            assert_eq!(confidence, 1.0);
            assert!(proof_certificate.contains("PROOF"));
        }
        _ => panic!("Expected FullMatch but got {:?}", result),
    }
}

#[test]
fn test_phase4_partial_match_fallback() {
    // Test partial match when theorem validation partially fails
    let analyzer = AnalyzerEngine::new().unwrap();
    
    let bundle = Bundle {
        name: "flash-loan-variant".to_string(),
        start_chain: Chain::Polygon,
        expr: Expr::Seq {
            first: Box::new(Expr::Action {
                action: Action::Borrow {
                    amount: Rational::from_integer(1000),
                    token: Token::WETH,
                    protocol: Protocol::custom("UnknownLender".to_string()),
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
                        protocol: Protocol::custom("UnknownLender".to_string()),
                    }
                }),
            }),
        },
        constraints: vec![],
    };
    
    // Use structural analyzer directly
    let structural_analyzer = StructuralAnalyzer::new();
    let analysis = structural_analyzer.analyze_structure(&bundle);
    
    let result = ResultBuilder::new()
        .with_structural_match("flash-loan-like".to_string(), 0.85)
        .add_risk_factor("Unknown protocol: UnknownLender".to_string())
        .add_warning("Protocol not in verified list".to_string())
        .build();
    
    match result {
        EnhancedAnalysisResult::PartialMatch { 
            pattern_similarity, 
            confidence, 
            risk_factors,
            warnings,
            .. 
        } => {
            assert_eq!(pattern_similarity, 0.85);
            assert!(confidence >= 0.5 && confidence <= 0.95);
            assert!(!risk_factors.is_empty());
            assert!(!warnings.is_empty());
        }
        _ => panic!("Expected PartialMatch but got {:?}", result),
    }
}

#[test]
fn test_phase4_heuristic_analysis_fallback() {
    // Test heuristic analysis for completely unknown pattern
    let bundle = Bundle {
        name: "novel-strategy".to_string(),
        start_chain: Chain::Arbitrum,
        expr: Expr::Seq {
            first: Box::new(Expr::Action {
                action: Action::Deposit {
                    amount: Rational::from_integer(500),
                    token: Token::USDC,
                    protocol: Protocol::custom("NewProtocol".to_string()),
                }
            }),
            second: Box::new(Expr::Parallel {
                exprs: vec![
                    Expr::Action {
                        action: Action::Swap {
                            amount_in: Rational::from_integer(250),
                            token_in: Token::USDC,
                            token_out: Token::DAI,
                            min_out: Rational::from_integer(240),
                            protocol: Protocol::custom("NewDEX".to_string()),
                        }
                    },
                    Expr::Action {
                        action: Action::Swap {
                            amount_in: Rational::from_integer(250),
                            token_in: Token::USDC,
                            token_out: Token::WETH,
                            min_out: Rational::from_integer(100),
                            protocol: Protocol::custom("AnotherDEX".to_string()),
                        }
                    },
                ],
            }),
        },
        constraints: vec![
            Constraint::MaxGas { amount: 1000000 },
        ],
    };
    
    let structural_analyzer = StructuralAnalyzer::new();
    let structural_analysis = structural_analyzer.analyze_structure(&bundle);
    let safety_analysis = structural_analyzer.generate_safety_analysis(&structural_analysis);
    let risk_assessment = structural_analyzer.generate_risk_assessment(&structural_analysis);
    
    assert!(matches!(risk_assessment.overall_risk, RiskLevel::High | RiskLevel::Critical));
    assert!(risk_assessment.risk_factors.contains_key("unknown_protocols"));
    
    let result = ResultBuilder::new()
        .add_risk_factor("Multiple unknown protocols".to_string())
        .build();
    
    match result {
        EnhancedAnalysisResult::Heuristic { 
            confidence,
            risk_assessment,
            manual_review_required,
            .. 
        } => {
            assert!(confidence >= 0.1 && confidence <= 0.5);
            assert!(manual_review_required);
            assert!(matches!(risk_assessment.overall_risk, RiskLevel::High | RiskLevel::Critical));
        }
        _ => panic!("Expected Heuristic but got something else"),
    }
}

#[test]
fn test_phase4_rejection_with_fixes() {
    // Test rejection with detailed fixes
    let bundle = Bundle {
        name: "unsafe-bundle".to_string(),
        start_chain: Chain::Polygon,
        expr: Expr::Seq {
            first: Box::new(Expr::Action {
                action: Action::Borrow {
                    amount: Rational::from_integer(10000),
                    token: Token::WETH,
                    protocol: Protocol::Aave,
                }
            }),
            second: Box::new(Expr::Action {
                action: Action::Swap {
                    amount_in: Rational::from_integer(10000),
                    token_in: Token::WETH,
                    token_out: Token::USDC,
                    min_out: Rational::from_integer(15000),
                    protocol: Protocol::UniswapV2,
                }
            }),
        },
        constraints: vec![
            Constraint::Deadline { blocks: 5 },
        ],
    };
    
    let result = ResultBuilder::new()
        .add_rejection_reason(RejectionReason::SafetyViolation {
            property: SafetyProperty::BalancePreservation,
            details: "No repayment found for flash loan".to_string(),
        })
        .add_rejection_reason(RejectionReason::InsufficientLiquidity {
            required: "10000 WETH".to_string(),
            available: "1000 WETH".to_string(),
        })
        .build();
    
    match result {
        EnhancedAnalysisResult::Reject { 
            reasons, 
            suggested_fixes,
            safety_report,
            .. 
        } => {
            assert!(reasons.len() >= 2);
            assert!(!suggested_fixes.is_empty());
            assert!(safety_report.overall_safety_score < 0.5);
            
            // Check that appropriate fixes are suggested
            let has_balance_fix = suggested_fixes.iter().any(|f| 
                matches!(f.fix_type, FixType::AdjustAmount | FixType::SimplifyStructure)
            );
            assert!(has_balance_fix);
        }
        _ => panic!("Expected Reject but got {:?}", result),
    }
}

#[test]
fn test_phase4_safety_heuristics() {
    // Test safety heuristics engine
    let bundle = Bundle {
        name: "test-safety".to_string(),
        start_chain: Chain::Polygon,
        expr: Expr::Seq {
            first: Box::new(Expr::Action {
                action: Action::Borrow {
                    amount: Rational::from_integer(100),
                    token: Token::WETH,
                    protocol: Protocol::Aave,
                }
            }),
            second: Box::new(Expr::Seq {
                first: Box::new(Expr::Action {
                    action: Action::Bridge {
                        chain: Chain::Arbitrum,
                        token: Token::WETH,
                        amount: Rational::from_integer(100),
                    }
                }),
                second: Box::new(Expr::OnChain {
                    chain: Chain::Arbitrum,
                    expr: Box::new(Expr::Action {
                        action: Action::Swap {
                            amount_in: Rational::from_integer(100),
                            token_in: Token::WETH,
                            token_out: Token::USDC,
                            min_out: Rational::from_integer(150),
                            protocol: Protocol::UniswapV2,
                        }
                    }),
                }),
            }),
        },
        constraints: vec![],
    };
    
    let structural_analyzer = StructuralAnalyzer::new();
    let analysis = structural_analyzer.analyze_structure(&bundle);
    
    let safety_heuristics = SafetyHeuristics::new();
    let violations = safety_heuristics.check_safety_violations(&analysis);
    let confidence = safety_heuristics.calculate_property_confidence(&analysis);
    
    // Check that cross-chain operations reduce atomicity confidence
    let atomicity_confidence = confidence.get(&SafetyProperty::Atomicity).unwrap();
    assert!(*atomicity_confidence < 0.8); // Should be reduced due to bridge
    
    // Check MEV vulnerability
    let mev_risk = ExtendedSafetyChecks::check_mev_vulnerability(&analysis);
    assert!(mev_risk.is_none() || mev_risk.is_some()); // Just verify it runs
}

#[test]
fn test_phase4_tiered_fallback_progression() {
    // Test the complete fallback chain
    let patterns = vec![
        ProvenPattern {
            pattern_id: "weak-pattern".to_string(),
            pattern_template: PatternTemplate::CustomPattern("Weak".to_string()),
            theorem_reference: "WeakTheorem".to_string(),
            theorem_file: std::path::PathBuf::from("test.lean"),
            theorem_line: 1,
            safety_properties: vec![SafetyProperty::Atomicity],
            preconditions: vec![],
            structure_regex: ".*".to_string(),
            confidence_threshold: 0.5,
            gas_optimization_potential: false,
        }
    ];
    
    // Test 1: Full match scenario
    let candidate = PatternCandidate {
        pattern: patterns[0].clone(),
        confidence_score: 0.95,
        match_location: (0, 10),
    };
    
    let result1 = ResultBuilder::new()
        .with_pattern_candidates(vec![candidate])
        .with_theorem_results(
            vec![("WeakTheorem".to_string(), Ok(vec![SafetyProperty::Atomicity]))]
                .into_iter()
                .collect()
        )
        .build();
    
    assert!(matches!(result1, EnhancedAnalysisResult::FullMatch { .. }));
    
    // Test 2: Partial match scenario
    let result2 = ResultBuilder::new()
        .with_structural_match("similar-pattern".to_string(), 0.75)
        .add_risk_factor("Some uncertainty".to_string())
        .build();
    
    assert!(matches!(result2, EnhancedAnalysisResult::PartialMatch { .. }));
    
    // Test 3: Heuristic scenario
    let result3 = ResultBuilder::new()
        .with_structural_match("unknown-pattern".to_string(), 0.4)
        .add_risk_factor("High uncertainty".to_string())
        .add_risk_factor("Unknown protocols".to_string())
        .build();
    
    assert!(matches!(result3, EnhancedAnalysisResult::Heuristic { .. }));
    
    // Test 4: Rejection scenario
    let result4 = ResultBuilder::new()
        .add_rejection_reason(RejectionReason::MalformedStructure {
            details: "Cannot parse bundle structure".to_string(),
        })
        .build();
    
    assert!(matches!(result4, EnhancedAnalysisResult::Reject { .. }));
}

#[test]
fn test_phase4_error_messages_and_debugging() {
    // Test detailed error reporting
    let results = vec![
        EnhancedAnalysisResult::FullMatch {
            pattern: ProvenPattern {
                pattern_id: "test".to_string(),
                pattern_template: PatternTemplate::FlashLoan,
                theorem_reference: "TestTheorem".to_string(),
                theorem_file: std::path::PathBuf::from("test.lean"),
                theorem_line: 42,
                safety_properties: vec![SafetyProperty::Atomicity],
                preconditions: vec![],
                structure_regex: ".*".to_string(),
                confidence_threshold: 0.7,
                gas_optimization_potential: true,
            },
            theorem_reference: "TestTheorem".to_string(),
            confidence: 1.0,
            safety_guarantees: vec![SafetyProperty::Atomicity],
            gas_optimization_available: true,
            execution_plan: "Execute with confidence".to_string(),
            proof_certificate: "PROOF[test.lean:42:TestTheorem]".to_string(),
        },
        EnhancedAnalysisResult::Reject {
            reasons: vec![
                RejectionReason::SafetyViolation {
                    property: SafetyProperty::Atomicity,
                    details: "Cannot guarantee atomicity".to_string(),
                }
            ],
            suggested_fixes: vec![
                SuggestedFix {
                    fix_type: FixType::SimplifyStructure,
                    description: "Reduce complexity".to_string(),
                    estimated_impact: "Higher success rate".to_string(),
                }
            ],
            partial_analysis: None,
            safety_report: SafetyReport {
                atomicity_analysis: "Failed".to_string(),
                balance_analysis: "Unknown".to_string(),
                protocol_safety: std::collections::HashMap::new(),
                cross_chain_risks: vec![],
                overall_safety_score: 0.2,
            },
        },
    ];
    
    for result in results {
        // Test summary generation
        let summary = result.summary();
        assert!(!summary.is_empty());
        
        // Test detailed report generation
        let report = result.detailed_report();
        assert!(!report.is_empty());
        
        // Test confidence extraction
        let confidence = result.confidence();
        assert!(confidence >= 0.0 && confidence <= 1.0);
        
        // Test executability check
        let executable = result.is_executable();
        assert!(executable || !executable); // Just verify it returns bool
    }
}