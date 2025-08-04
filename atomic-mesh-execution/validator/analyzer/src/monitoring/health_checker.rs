//! Health checking for analyzer system monitoring
//!
//! This module provides health checks to ensure the analyzer is functioning
//! correctly in production environments.

use std::time::Instant;
use crate::engine::AnalyzerEngine;
use crate::common::AnalysisResult;

/// Health status of the analyzer
#[derive(Debug, Clone, PartialEq)]
pub enum HealthStatus {
    /// System is healthy and operating normally
    Healthy {
        message: String,
        latency_ms: u64,
    },
    /// System is degraded but operational
    Degraded {
        message: String,
        issues: Vec<String>,
    },
    /// System is unhealthy and may not function correctly
    Unhealthy {
        message: String,
        errors: Vec<String>,
    },
}

/// Health checker for the analyzer system
pub struct HealthChecker {
    /// Maximum acceptable latency for health checks
    max_latency_ms: u64,
    /// Whether to perform deep health checks
    deep_check: bool,
}

impl HealthChecker {
    /// Create a new health checker
    pub fn new() -> Self {
        Self {
            max_latency_ms: 100, // 100ms max for health check
            deep_check: false,
        }
    }

    /// Enable deep health checks
    pub fn with_deep_checks(mut self) -> Self {
        self.deep_check = true;
        self
    }

    /// Set maximum acceptable latency
    pub fn with_max_latency_ms(mut self, max_latency_ms: u64) -> Self {
        self.max_latency_ms = max_latency_ms;
        self
    }

    /// Perform health check on the analyzer
    pub fn check_health(&self, analyzer: &mut AnalyzerEngine) -> HealthStatus {
        let start = Instant::now();
        let mut issues = Vec::new();
        let mut errors = Vec::new();

        // Check 1: Basic analyzer functionality
        match self.check_basic_functionality(analyzer) {
            Ok(()) => {},
            Err(e) => errors.push(format!("Basic functionality check failed: {}", e)),
        }

        // Check 2: Pattern library status
        match analyzer.get_pattern_count() {
            n if n == 0 => issues.push("No patterns loaded".to_string()),
            n if n < 5 => issues.push(format!("Only {} patterns loaded", n)),
            _ => {},
        }

        // Check 3: Performance check (if deep check enabled)
        if self.deep_check {
            match self.check_performance(analyzer) {
                Ok(perf_ms) => {
                    if perf_ms > 5 {
                        issues.push(format!("Performance degraded: {}ms for test bundle", perf_ms));
                    }
                },
                Err(e) => errors.push(format!("Performance check failed: {}", e)),
            }
        }

        // Check 4: Memory usage (placeholder - would need actual implementation)
        // In a real system, we'd check memory usage here

        let elapsed = start.elapsed();
        let latency_ms = elapsed.as_millis() as u64;

        // Check if health check itself took too long
        if latency_ms > self.max_latency_ms {
            issues.push(format!("Health check latency {}ms exceeds max {}ms", 
                              latency_ms, self.max_latency_ms));
        }

        // Determine overall health status
        if !errors.is_empty() {
            HealthStatus::Unhealthy {
                message: "Analyzer is unhealthy".to_string(),
                errors,
            }
        } else if !issues.is_empty() {
            HealthStatus::Degraded {
                message: "Analyzer is operational but degraded".to_string(),
                issues,
            }
        } else {
            HealthStatus::Healthy {
                message: "Analyzer is healthy".to_string(),
                latency_ms,
            }
        }
    }

    /// Check basic analyzer functionality
    fn check_basic_functionality(&self, analyzer: &mut AnalyzerEngine) -> Result<(), String> {
        // Create a simple test bundle
        use common::types::{Bundle, Expr, Action, Token, Protocol, Chain, Rational};
        
        let test_bundle = Bundle {
            name: "health_check".to_string(),
            start_chain: Chain::Polygon,
            expr: Expr::Action {
                action: Action::Swap {
                    protocol: Protocol::UniswapV2,
                    token_in: Token::WETH,
                    token_out: Token::USDC,
                    amount_in: Rational::from_integer(1),
                    min_out: Rational::from_integer(1),
                }
            },
            constraints: vec![],
        };

        // Try to analyze it
        match analyzer.analyze_bundle(&test_bundle) {
            AnalysisResult::FullMatch { .. } |
            AnalysisResult::PartialMatch { .. } |
            AnalysisResult::Heuristic { .. } => Ok(()),
            AnalysisResult::Reject { error, .. } => {
                // It's OK if it's rejected, as long as the analyzer didn't crash
                Ok(())
            }
        }
    }

    /// Check analyzer performance
    fn check_performance(&self, analyzer: &mut AnalyzerEngine) -> Result<u64, String> {
        use common::types::{Bundle, Expr, Action, Token, Protocol, Chain, Rational, Constraint};
        
        // Create a more complex test bundle
        let test_bundle = Bundle {
            name: "perf_check".to_string(),
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
                        action: Action::Swap {
                            amount_in: Rational::from_integer(100),
                            token_in: Token::WETH,
                            token_out: Token::USDC,
                            min_out: Rational::from_integer(150),
                            protocol: Protocol::UniswapV2,
                        }
                    }),
                    second: Box::new(Expr::Action {
                        action: Action::Repay {
                            amount: Rational::from_integer(100),
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

        let start = Instant::now();
        let _ = analyzer.analyze_bundle(&test_bundle);
        let elapsed = start.elapsed();
        
        Ok(elapsed.as_millis() as u64)
    }

    /// Get a human-readable health report
    pub fn get_health_report(&self, status: &HealthStatus) -> String {
        match status {
            HealthStatus::Healthy { message, latency_ms } => {
                format!("✅ HEALTHY\n{}\nHealth check latency: {}ms", message, latency_ms)
            },
            HealthStatus::Degraded { message, issues } => {
                format!("⚠️  DEGRADED\n{}\nIssues:\n{}", 
                       message, 
                       issues.iter().map(|i| format!("- {}", i)).collect::<Vec<_>>().join("\n"))
            },
            HealthStatus::Unhealthy { message, errors } => {
                format!("❌ UNHEALTHY\n{}\nErrors:\n{}", 
                       message,
                       errors.iter().map(|e| format!("- {}", e)).collect::<Vec<_>>().join("\n"))
            },
        }
    }
}

impl Default for HealthChecker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_health_status_equality() {
        let status1 = HealthStatus::Healthy { 
            message: "OK".to_string(), 
            latency_ms: 10 
        };
        let status2 = HealthStatus::Healthy { 
            message: "OK".to_string(), 
            latency_ms: 10 
        };
        assert_eq!(status1, status2);
    }

    #[test]
    fn test_health_checker_creation() {
        let checker = HealthChecker::new();
        assert_eq!(checker.max_latency_ms, 100);
        assert!(!checker.deep_check);
        
        let deep_checker = HealthChecker::new()
            .with_deep_checks()
            .with_max_latency_ms(50);
        assert!(deep_checker.deep_check);
        assert_eq!(deep_checker.max_latency_ms, 50);
    }

    #[test]
    fn test_health_report_formatting() {
        let checker = HealthChecker::new();
        
        let healthy = HealthStatus::Healthy {
            message: "All good".to_string(),
            latency_ms: 5,
        };
        let report = checker.get_health_report(&healthy);
        assert!(report.contains("✅ HEALTHY"));
        assert!(report.contains("5ms"));
        
        let degraded = HealthStatus::Degraded {
            message: "Some issues".to_string(),
            issues: vec!["Issue 1".to_string(), "Issue 2".to_string()],
        };
        let report = checker.get_health_report(&degraded);
        assert!(report.contains("⚠️  DEGRADED"));
        assert!(report.contains("Issue 1"));
        assert!(report.contains("Issue 2"));
    }
}