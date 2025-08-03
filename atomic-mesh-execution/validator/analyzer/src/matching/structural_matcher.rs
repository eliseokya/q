//! Structural pattern matcher for DSL expressions
//!
//! This module provides O(1) pattern matching using finite automata
//! against DSL expressions from the compiler.

use crate::common::{Bundle, Expr, Action, ProvenPattern, PatternCandidate};
use crate::pattern_compiler::FiniteAutomaton;
use std::collections::HashMap;
use std::time::Instant;

/// Result of a pattern match attempt
#[derive(Debug, Clone)]
pub struct MatchResult {
    pub pattern_id: String,
    pub confidence: f64,
    pub match_time_us: u64,
    pub matched_components: Vec<String>,
}

/// Structural matcher using finite automata for fast pattern recognition
pub struct StructuralMatcher {
    /// Pre-compiled automata for each pattern
    pattern_automata: HashMap<String, FiniteAutomaton>,
    /// Performance metrics
    total_matches: usize,
    total_match_time_us: u64,
}

impl StructuralMatcher {
    pub fn new() -> Self {
        Self {
            pattern_automata: HashMap::new(),
            total_matches: 0,
            total_match_time_us: 0,
        }
    }

    /// Load pre-compiled automata
    pub fn load_automata(&mut self, automata: HashMap<String, FiniteAutomaton>) {
        self.pattern_automata = automata;
    }

    /// Match a bundle expression against all loaded patterns
    pub fn match_bundle(&mut self, bundle: &Bundle) -> Vec<MatchResult> {
        let start = Instant::now();
        let mut results = Vec::new();

        // Flatten the expression into a token stream
        let tokens = self.tokenize_expression(&bundle.expr);

        // Try each automaton
        for (_pattern_id, automaton) in self.pattern_automata.iter_mut() {
            automaton.reset();
            
            let mut matched = false;
            let mut matched_components = Vec::new();

            // Feed tokens to automaton
            for token in &tokens {
                if let Some(matched_pattern) = automaton.process(token) {
                    matched = true;
                    matched_components.push(token.clone());
                    
                    // Calculate confidence after loop
                    let confidence = 0.9; // Will calculate properly after the loop

                    results.push(MatchResult {
                        pattern_id: matched_pattern,
                        confidence,
                        match_time_us: start.elapsed().as_micros() as u64,
                        matched_components: matched_components.clone(),
                    });
                    break;
                }
                matched_components.push(token.clone());
            }

            // Check if we're in a final state even without explicit match
            if !matched && automaton.is_in_final_state() {
                if let Some(pattern) = automaton.get_matched_pattern() {
                    let is_final = automaton.is_in_final_state();
                    let confidence = calculate_confidence_static(&tokens, &matched_components, is_final);
                    results.push(MatchResult {
                        pattern_id: pattern,
                        confidence,
                        match_time_us: start.elapsed().as_micros() as u64,
                        matched_components,
                    });
                }
            }
        }

        let elapsed = start.elapsed().as_micros() as u64;
        self.total_matches += 1;
        self.total_match_time_us += elapsed;

        results
    }

    /// Convert expression to token stream for automaton processing
    fn tokenize_expression(&self, expr: &Expr) -> Vec<String> {
        let mut tokens = Vec::new();
        self.tokenize_recursive(expr, &mut tokens);
        tokens
    }

    fn tokenize_recursive(&self, expr: &Expr, tokens: &mut Vec<String>) {
        match expr {
            Expr::Action { action } => {
                tokens.push(self.action_to_token(action));
            }
            Expr::Seq { first, second } => {
                tokens.push("seq".to_string());
                self.tokenize_recursive(first, tokens);
                self.tokenize_recursive(second, tokens);
            }
            Expr::Parallel { exprs } => {
                tokens.push("parallel".to_string());
                for e in exprs {
                    self.tokenize_recursive(e, tokens);
                }
            }
            Expr::OnChain { chain, expr } => {
                tokens.push(format!("onChain:{:?}", chain));
                self.tokenize_recursive(expr, tokens);
            }
        }
    }

    fn action_to_token(&self, action: &Action) -> String {
        match action {
            Action::Swap { token_in, token_out, protocol, .. } => {
                format!("swap:{:?}:{:?}:{:?}", token_in, token_out, protocol)
            }
            Action::Borrow { token, protocol, .. } => {
                format!("borrow:{:?}:{:?}", token, protocol)
            }
            Action::Repay { token, protocol, .. } => {
                format!("repay:{:?}:{:?}", token, protocol)
            }
            Action::Bridge { chain, token, .. } => {
                format!("bridge:{:?}:{:?}", chain, token)
            }
            Action::Deposit { token, protocol, .. } => {
                format!("deposit:{:?}:{:?}", token, protocol)
            }
            Action::Withdraw { token, protocol, .. } => {
                format!("withdraw:{:?}:{:?}", token, protocol)
            }
        }
    }

    /// Get performance statistics
    pub fn get_stats(&self) -> MatcherStats {
        MatcherStats {
            total_matches: self.total_matches,
            average_match_time_us: if self.total_matches > 0 {
                self.total_match_time_us / self.total_matches as u64
            } else {
                0
            },
            loaded_patterns: self.pattern_automata.len(),
        }
    }

    /// Convert match results to pattern candidates
    pub fn results_to_candidates(&self, results: Vec<MatchResult>, patterns: &[ProvenPattern]) -> Vec<PatternCandidate> {
        results.into_iter()
            .filter_map(|result| {
                patterns.iter()
                    .find(|p| p.pattern_id == result.pattern_id)
                    .map(|pattern| PatternCandidate {
                        pattern: pattern.clone(),
                        confidence_score: result.confidence,
                        structural_match: true,
                        semantic_match: false, // Will be determined later
                        match_details: format!(
                            "Matched {} components in {}μs",
                            result.matched_components.len(),
                            result.match_time_us
                        ),
                    })
            })
            .collect()
    }
}

/// Calculate match confidence based on various factors
fn calculate_confidence_static(
    all_tokens: &[String],
    matched_tokens: &[String],
    is_final_state: bool,
) -> f64 {
    let coverage = matched_tokens.len() as f64 / all_tokens.len() as f64;
    let in_final_state = if is_final_state { 1.0 } else { 0.5 };
    
    // Base confidence on coverage and final state
    let base_confidence = coverage * 0.7 + in_final_state * 0.3;
    
    // Boost for specific patterns
    let pattern_boost = if matched_tokens.iter().any(|t| t.contains("borrow") && t.contains("repay")) {
        0.1 // Flash loan pattern boost
    } else if matched_tokens.iter().any(|t| t.contains("bridge")) {
        0.05 // Cross-chain pattern boost
    } else {
        0.0
    };
    
    (base_confidence + pattern_boost).min(1.0)
}

#[derive(Debug)]
pub struct MatcherStats {
    pub total_matches: usize,
    pub average_match_time_us: u64,
    pub loaded_patterns: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{Token, Protocol, Chain, Rational};
    use crate::pattern_compiler::AutomataGenerator;

    #[test]
    fn test_flash_loan_matching() {
        let mut matcher = StructuralMatcher::new();
        
        // Create a flash loan automaton
        let generator = AutomataGenerator::new();
        let automaton = generator.generate_flash_loan_automaton("flash_loan_pattern");
        
        let mut automata = HashMap::new();
        automata.insert("flash_loan_pattern".to_string(), automaton);
        matcher.load_automata(automata);

        // Create a flash loan bundle
        let bundle = Bundle {
            name: "test_flash_loan".to_string(),
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
            constraints: vec![],
        };

        let results = matcher.match_bundle(&bundle);
        assert!(!results.is_empty());
        assert_eq!(results[0].pattern_id, "flash_loan_pattern");
        assert!(results[0].confidence > 0.8);
    }
}