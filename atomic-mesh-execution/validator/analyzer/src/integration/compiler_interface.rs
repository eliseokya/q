//! Interface for communication with the DSL compiler
//!
//! This module handles the stdin/stdout protocol for receiving bundles
//! from the compiler and sending analysis results to the proof verifier.

use crate::common::{Bundle, AnalysisResult};
use crate::engine::AnalyzerEngine;
use serde::{Deserialize, Serialize};
use std::io::{self, BufRead, BufReader, Write};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum InterfaceError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),
    
    #[error("JSON parsing error: {0}")]
    Json(#[from] serde_json::Error),
    
    #[error("Invalid message format: {0}")]
    InvalidFormat(String),
    
    #[error("Analyzer error: {0}")]
    AnalyzerError(String),
}

/// Message types from the compiler
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum CompilerMessage {
    /// New bundle to analyze
    AnalyzeBundle {
        id: String,
        bundle: Bundle,
    },
    
    /// Request for analyzer status
    StatusRequest,
    
    /// Shutdown command
    Shutdown,
}

/// Response types to the compiler/proof verifier
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum AnalyzerResponse {
    /// Analysis result for a bundle
    AnalysisResult {
        id: String,
        result: AnalysisResultDTO,
        timing_us: u64,
    },
    
    /// Status response
    Status {
        healthy: bool,
        patterns_loaded: usize,
        analyses_completed: u64,
        average_latency_us: u64,
    },
    
    /// Acknowledgment of shutdown
    ShutdownAck,
    
    /// Error response
    Error {
        message: String,
    },
}

/// Data Transfer Object for AnalysisResult (proof verifier compatible)
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "verdict", rename_all = "snake_case")]
pub enum AnalysisResultDTO {
    /// Bundle is valid with mathematical proof
    Valid {
        theorem_reference: String,
        confidence: f64,
        safety_guarantees: Vec<String>,
        gas_optimization_available: bool,
        execution_plan: String,
    },
    
    /// Bundle needs manual review
    NeedsReview {
        confidence: f64,
        concerns: Vec<String>,
        suggested_fixes: Vec<String>,
    },
    
    /// Bundle is rejected
    Rejected {
        reason: String,
        details: String,
    },
}

/// Interface for compiler communication
pub struct CompilerInterface {
    analyzer: AnalyzerEngine,
    total_analyses: u64,
    total_time_us: u64,
}

impl CompilerInterface {
    /// Create a new compiler interface
    pub fn new(analyzer: AnalyzerEngine) -> Self {
        Self {
            analyzer,
            total_analyses: 0,
            total_time_us: 0,
        }
    }
    
    /// Run the interface, reading from stdin and writing to stdout
    pub fn run(&mut self) -> Result<(), InterfaceError> {
        let stdin = io::stdin();
        let reader = BufReader::new(stdin.lock());
        let mut stdout = io::stdout();
        
        for line in reader.lines() {
            let line = line?;
            if line.trim().is_empty() {
                continue;
            }
            
            // Parse the message
            let message: CompilerMessage = serde_json::from_str(&line)
                .map_err(|e| InterfaceError::InvalidFormat(format!("Failed to parse: {}", e)))?;
            
            // Process the message
            let response = self.process_message(message)?;
            
            // Send the response
            let response_json = serde_json::to_string(&response)?;
            writeln!(stdout, "{}", response_json)?;
            stdout.flush()?;
            
            // Check for shutdown
            if matches!(response, AnalyzerResponse::ShutdownAck) {
                break;
            }
        }
        
        Ok(())
    }
    
    /// Process a single message from the compiler
    pub fn process_message(&mut self, message: CompilerMessage) -> Result<AnalyzerResponse, InterfaceError> {
        match message {
            CompilerMessage::AnalyzeBundle { id, bundle } => {
                // Time the analysis
                let start = std::time::Instant::now();
                let result = self.analyzer.analyze_bundle(&bundle);
                let elapsed = start.elapsed();
                let timing_us = elapsed.as_micros() as u64;
                
                // Update statistics
                self.total_analyses += 1;
                self.total_time_us += timing_us;
                
                // Convert to DTO
                let result_dto = Self::convert_result(result);
                
                Ok(AnalyzerResponse::AnalysisResult {
                    id,
                    result: result_dto,
                    timing_us,
                })
            }
            
            CompilerMessage::StatusRequest => {
                let average_latency = if self.total_analyses > 0 {
                    self.total_time_us / self.total_analyses
                } else {
                    0
                };
                
                Ok(AnalyzerResponse::Status {
                    healthy: true,
                    patterns_loaded: self.analyzer.get_pattern_count(),
                    analyses_completed: self.total_analyses,
                    average_latency_us: average_latency,
                })
            }
            
            CompilerMessage::Shutdown => {
                Ok(AnalyzerResponse::ShutdownAck)
            }
        }
    }
    
    /// Convert internal AnalysisResult to DTO format
    fn convert_result(result: AnalysisResult) -> AnalysisResultDTO {
        match result {
            AnalysisResult::FullMatch {
                theorem_reference,
                confidence,
                safety_guarantees,
                gas_optimization_available,
                execution_plan,
            } => AnalysisResultDTO::Valid {
                theorem_reference,
                confidence,
                safety_guarantees: safety_guarantees.into_iter()
                    .map(|g| format!("{:?}", g))
                    .collect(),
                gas_optimization_available,
                execution_plan,
            },
            
            AnalysisResult::PartialMatch {
                confidence,
                missing_guarantees,
                recommendation,
                ..
            } => AnalysisResultDTO::NeedsReview {
                confidence,
                concerns: missing_guarantees.into_iter()
                    .map(|g| format!("Missing guarantee: {:?}", g))
                    .collect(),
                suggested_fixes: vec![format!("{:?}", recommendation)],
            },
            
            AnalysisResult::Heuristic {
                safety_warnings,
                confidence,
                ..
            } => AnalysisResultDTO::NeedsReview {
                confidence,
                concerns: safety_warnings,
                suggested_fixes: vec!["Manual review recommended".to_string()],
            },
            
            AnalysisResult::Reject { error, .. } => {
                AnalysisResultDTO::Rejected {
                    reason: error.to_string(),
                    details: "Bundle validation failed".to_string(),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{Expr, Action, Chain, Protocol, Token, Rational};
    
    #[test]
    fn test_message_serialization() {
        let message = CompilerMessage::AnalyzeBundle {
            id: "test-123".to_string(),
            bundle: Bundle {
                name: "test".to_string(),
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
            },
        };
        
        let json = serde_json::to_string(&message).unwrap();
        assert!(json.contains("analyze_bundle"));
        assert!(json.contains("test-123"));
        
        let parsed: CompilerMessage = serde_json::from_str(&json).unwrap();
        match parsed {
            CompilerMessage::AnalyzeBundle { id, .. } => {
                assert_eq!(id, "test-123");
            }
            _ => panic!("Wrong message type"),
        }
    }
    
    #[test]
    fn test_response_serialization() {
        let response = AnalyzerResponse::AnalysisResult {
            id: "test-123".to_string(),
            result: AnalysisResultDTO::Valid {
                theorem_reference: "theorem_123".to_string(),
                confidence: 0.95,
                safety_guarantees: vec!["NoReentrancy".to_string()],
                gas_optimization_available: true,
                execution_plan: "Execute via flash loan".to_string(),
            },
            timing_us: 150,
        };
        
        let json = serde_json::to_string(&response).unwrap();
        assert!(json.contains("analysis_result"));
        assert!(json.contains("valid"));
        assert!(json.contains("theorem_123"));
    }
}