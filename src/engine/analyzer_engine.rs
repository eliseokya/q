//! Main analyzer engine that orchestrates pattern matching and analysis
//! 
//! This is the central component that coordinates all aspects of bundle analysis,
//! from pattern matching through the tiered fallback system.

use std::collections::HashMap;
use std::time::{Duration, Instant};
use serde::{Deserialize, Serialize};

use crate::common::{
    Bundle, AnalysisResult, ProvenPattern, PatternMatch, SafetyProperty,
    ValidationError, BundleAnalysis, ComplexityEstimate, RiskProfile, RiskFactor,
};

/// High-performance analyzer engine that orchestrates pattern matching
#[derive(Debug)]
pub struct AnalyzerEngine {
    /// Static pattern library loaded at startup
    pattern_library: StaticPatternLibrary,
    
    /// Dynamic cache for runtime optimization
    pattern_cache: DynamicPatternCache,
    
    /// Performance monitoring and timing
    performance_monitor: PerformanceMonitor,
    
    /// Configuration settings
    config: AnalyzerConfig,
}

/// Static pattern library containing pre-compiled patterns
#[derive(Debug, Clone)]
pub struct StaticPatternLibrary {
    /// All proven patterns organized by type
    patterns: HashMap<PatternType, Vec<ProvenPattern>>,
    
    /// Fast lookup index by pattern ID
    pattern_index: HashMap<String, ProvenPattern>,
    
    /// Patterns ordered by success rate for optimization
    ordered_patterns: Vec<String>,
}

/// Dynamic pattern cache for runtime optimization
#[derive(Debug)]
pub struct DynamicPatternCache {
    /// Recent successful matches (LRU cache)
    recent_matches: lru::LruCache<String, PatternMatch>,
    
    /// Negative cache for known non-matches
    negative_cache: std::collections::HashSet<String>,
    
    /// Pattern performance statistics
    pattern_stats: HashMap<String, PatternStats>,
}

/// Performance monitoring for the analyzer
#[derive(Debug)]
pub struct PerformanceMonitor {
    /// Total number of analyses performed
    total_analyses: u64,
    
    /// Performance timing checkpoints
    timing_checkpoints: Vec<(String, Duration)>,
    
    /// Current analysis start time
    current_analysis_start: Option<Instant>,
}

/// Configuration for the analyzer engine
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AnalyzerConfig {
    /// Maximum time allowed for analysis (microseconds)
    pub max_analysis_time_us: u64,
    
    /// Cache size for recent matches
    pub cache_size: usize,
    
    /// Whether to enable performance monitoring
    pub enable_monitoring: bool,
    
    /// Confidence threshold for partial matches
    pub partial_match_threshold: f64,
    
    /// Risk threshold for heuristic analysis
    pub risk_threshold: f64,
}

/// Types of patterns for organization
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum PatternType {
    FlashLoan,
    CrossChainArbitrage,
    SimpleArbitrage,
    Liquidation,
    YieldFarming,
    Other,
}

/// Performance statistics for individual patterns
#[derive(Debug, Clone)]
pub struct PatternStats {
    /// Number of times this pattern was attempted
    pub attempts: u64,
    
    /// Number of successful matches
    pub successes: u64,
    
    /// Average matching time in microseconds
    pub avg_time_us: u64,
    
    /// Last used timestamp
    pub last_used: Instant,
}

/// Detailed analysis context during processing
#[derive(Debug)]
pub struct AnalysisContext {
    /// The bundle being analyzed
    pub bundle: Bundle,
    
    /// Hash of the bundle for caching
    pub bundle_hash: String,
    
    /// Start time of analysis
    pub start_time: Instant,
    
    /// Performance checkpoints
    pub checkpoints: Vec<(String, Duration)>,
    
    /// Partial analysis results
    pub partial_results: Vec<PatternMatch>,
}

impl AnalyzerEngine {
    /// Create a new analyzer engine with default configuration
    pub fn new() -> Result<Self, ValidationError> {
        let config = AnalyzerConfig::default();
        Self::with_config(config)
    }
    
    /// Create a new analyzer engine with custom configuration
    pub fn with_config(config: AnalyzerConfig) -> Result<Self, ValidationError> {
        let pattern_library = StaticPatternLibrary::load()?;
        let pattern_cache = DynamicPatternCache::new(config.cache_size);
        let performance_monitor = PerformanceMonitor::new();
        
        Ok(Self {
            pattern_library,
            pattern_cache,
            performance_monitor,
            config,
        })
    }
    
    /// Analyze a bundle through the complete tiered fallback system
    pub fn analyze(&mut self, bundle: Bundle) -> AnalysisResult {
        let analysis_start = Instant::now();
        let bundle_hash = self.calculate_bundle_hash(&bundle);
        
        // Check cache first
        if let Some(cached_result) = self.check_cache(&bundle_hash) {
            return cached_result;
        }
        
        let mut context = AnalysisContext::new(bundle.clone(), bundle_hash.clone(), analysis_start);
        
        // Performance timeout check
        let timeout = Duration::from_micros(self.config.max_analysis_time_us);
        
        // Tier 1: Try for full pattern match
        if let Some(result) = self.attempt_full_match(&mut context) {
            self.cache_result(&bundle_hash, &result);
            return result;
        }
        
        // Check timeout
        if context.start_time.elapsed() > timeout {
            return self.handle_timeout(context);
        }
        
        // Tier 2: Try for partial pattern match
        if let Some(result) = self.attempt_partial_match(&mut context) {
            self.cache_result(&bundle_hash, &result);
            return result;
        }
        
        // Check timeout
        if context.start_time.elapsed() > timeout {
            return self.handle_timeout(context);
        }
        
        // Tier 3: Heuristic analysis
        if let Some(result) = self.attempt_heuristic_analysis(&mut context) {
            return result;
        }
        
        // Tier 4: Rejection with analysis
        self.generate_rejection(context)
    }
    
    /// Attempt to find a complete pattern match (Tier 1)
    fn attempt_full_match(&mut self, context: &mut AnalysisContext) -> Option<AnalysisResult> {
        // This will be implemented in the pattern matching module
        // For now, return None to proceed to partial matching
        None
    }
    
    /// Attempt to find a partial pattern match (Tier 2)
    fn attempt_partial_match(&mut self, context: &mut AnalysisContext) -> Option<AnalysisResult> {
        // This will be implemented in the pattern matching module
        // For now, return None to proceed to heuristic analysis
        None
    }
    
    /// Perform heuristic analysis (Tier 3)
    fn attempt_heuristic_analysis(&mut self, context: &mut AnalysisContext) -> Option<AnalysisResult> {
        let bundle_analysis = self.analyze_bundle_properties(&context.bundle);
        let risk_factors = self.assess_risk_factors(&context.bundle, &bundle_analysis);
        
        let overall_risk = self.calculate_overall_risk(&risk_factors);
        let risk_profile = RiskProfile::new(overall_risk, risk_factors, 0.7);
        
        Some(AnalysisResult::heuristic(
            risk_profile,
            0.3, // Low confidence for heuristic analysis
            vec![], // No specific patterns detected
            vec!["Unknown pattern structure".to_string()],
            true, // Manual review required
        ))
    }
    
    /// Generate a rejection result (Tier 4)
    fn generate_rejection(&self, context: AnalysisContext) -> AnalysisResult {
        let bundle_analysis = self.analyze_bundle_properties(&context.bundle);
        let error = ValidationError::UnknownPattern;
        let suggested_fixes = vec![
            "Consider simplifying the bundle structure".to_string(),
            "Ensure all actions follow known patterns".to_string(),
        ];
        
        AnalysisResult::reject(
            error,
            context.bundle_hash,
            bundle_analysis,
            suggested_fixes,
        )
    }
    
    /// Handle analysis timeout
    fn handle_timeout(&self, context: AnalysisContext) -> AnalysisResult {
        let bundle_analysis = self.analyze_bundle_properties(&context.bundle);
        let error = ValidationError::PerformanceTimeout {
            timeout_ms: self.config.max_analysis_time_us / 1000,
        };
        
        AnalysisResult::reject(
            error,
            context.bundle_hash,
            bundle_analysis,
            vec!["Consider reducing bundle complexity".to_string()],
        )
    }
    
    /// Calculate a hash of the bundle for caching
    fn calculate_bundle_hash(&self, bundle: &Bundle) -> String {
        // Simple hash implementation - in production, use a proper hash function
        format!("bundle_{}", bundle.name)
    }
    
    /// Check the cache for a previous analysis result
    fn check_cache(&mut self, bundle_hash: &str) -> Option<AnalysisResult> {
        // Check negative cache first
        if self.pattern_cache.negative_cache.contains(bundle_hash) {
            return None;
        }
        
        // Check positive cache
        self.pattern_cache.recent_matches.get(bundle_hash).map(|pattern_match| {
            AnalysisResult::full_match(
                pattern_match.clone(),
                pattern_match.theorem_reference().to_string(),
                pattern_match.verified_properties.clone(),
            )
        })
    }
    
    /// Cache an analysis result
    fn cache_result(&mut self, bundle_hash: &str, result: &AnalysisResult) {
        match result {
            AnalysisResult::FullMatch { pattern_match, .. } => {
                self.pattern_cache.recent_matches.put(bundle_hash.to_string(), pattern_match.clone());
            }
            AnalysisResult::Reject { .. } => {
                self.pattern_cache.negative_cache.insert(bundle_hash.to_string());
            }
            _ => {
                // Don't cache partial matches or heuristic results
            }
        }
    }
    
    /// Analyze basic properties of a bundle
    fn analyze_bundle_properties(&self, bundle: &Bundle) -> BundleAnalysis {
        // Extract basic information from the bundle
        let action_count = self.count_actions(&bundle.expr);
        let chains_involved = self.extract_chains(&bundle.expr);
        let tokens_involved = self.extract_tokens(&bundle.expr);
        let protocols_involved = self.extract_protocols(&bundle.expr);
        
        let complexity_estimate = ComplexityEstimate {
            time_complexity: "O(n)".to_string(),
            space_complexity: "O(1)".to_string(),
            estimated_time_us: action_count as u64 * 50, // 50μs per action estimate
            estimated_memory_bytes: 1024, // 1KB estimate
        };
        
        BundleAnalysis {
            action_count,
            chains_involved: chains_involved.clone(),
            tokens_involved,
            protocols_involved,
            complexity_estimate,
            has_cross_chain: chains_involved.len() > 1,
            has_parallel: self.has_parallel_expr(&bundle.expr),
        }
    }
    
    /// Count the number of actions in an expression
    fn count_actions(&self, expr: &crate::common::Expr) -> usize {
        match expr {
            crate::common::Expr::Action { .. } => 1,
            crate::common::Expr::Seq { e1, e2 } => {
                self.count_actions(e1) + self.count_actions(e2)
            }
            crate::common::Expr::Parallel { exprs } => {
                exprs.iter().map(|e| self.count_actions(e)).sum()
            }
            crate::common::Expr::OnChain { expr, .. } => {
                self.count_actions(expr)
            }
        }
    }
    
    /// Extract chains involved in an expression
    fn extract_chains(&self, expr: &crate::common::Expr) -> Vec<crate::common::Chain> {
        let mut chains = Vec::new();
        self.extract_chains_recursive(expr, &mut chains);
        chains.sort();
        chains.dedup();
        chains
    }
    
    fn extract_chains_recursive(&self, expr: &crate::common::Expr, chains: &mut Vec<crate::common::Chain>) {
        match expr {
            crate::common::Expr::Action { action } => {
                if let crate::common::Action::Bridge { chain, .. } = action {
                    chains.push(chain.clone());
                }
            }
            crate::common::Expr::Seq { e1, e2 } => {
                self.extract_chains_recursive(e1, chains);
                self.extract_chains_recursive(e2, chains);
            }
            crate::common::Expr::Parallel { exprs } => {
                for expr in exprs {
                    self.extract_chains_recursive(expr, chains);
                }
            }
            crate::common::Expr::OnChain { chain, expr } => {
                chains.push(chain.clone());
                self.extract_chains_recursive(expr, chains);
            }
        }
    }
    
    /// Extract tokens involved in an expression
    fn extract_tokens(&self, expr: &crate::common::Expr) -> Vec<crate::common::Token> {
        let mut tokens = Vec::new();
        self.extract_tokens_recursive(expr, &mut tokens);
        tokens.sort_by_key(|t| format!("{:?}", t));
        tokens.dedup();
        tokens
    }
    
    fn extract_tokens_recursive(&self, expr: &crate::common::Expr, tokens: &mut Vec<crate::common::Token>) {
        match expr {
            crate::common::Expr::Action { action } => {
                match action {
                    crate::common::Action::Borrow { token, .. } |
                    crate::common::Action::Repay { token, .. } |
                    crate::common::Action::Deposit { token, .. } |
                    crate::common::Action::Withdraw { token, .. } |
                    crate::common::Action::Bridge { token, .. } |
                    crate::common::Action::Transfer { token, .. } => {
                        tokens.push(token.clone());
                    }
                    crate::common::Action::Swap { token_in, token_out, .. } => {
                        tokens.push(token_in.clone());
                        tokens.push(token_out.clone());
                    }
                }
            }
            crate::common::Expr::Seq { e1, e2 } => {
                self.extract_tokens_recursive(e1, tokens);
                self.extract_tokens_recursive(e2, tokens);
            }
            crate::common::Expr::Parallel { exprs } => {
                for expr in exprs {
                    self.extract_tokens_recursive(expr, tokens);
                }
            }
            crate::common::Expr::OnChain { expr, .. } => {
                self.extract_tokens_recursive(expr, tokens);
            }
        }
    }
    
    /// Extract protocols involved in an expression
    fn extract_protocols(&self, expr: &crate::common::Expr) -> Vec<crate::common::Protocol> {
        let mut protocols = Vec::new();
        self.extract_protocols_recursive(expr, &mut protocols);
        protocols.sort_by_key(|p| format!("{:?}", p));
        protocols.dedup();
        protocols
    }
    
    fn extract_protocols_recursive(&self, expr: &crate::common::Expr, protocols: &mut Vec<crate::common::Protocol>) {
        match expr {
            crate::common::Expr::Action { action } => {
                match action {
                    crate::common::Action::Borrow { protocol, .. } |
                    crate::common::Action::Repay { protocol, .. } |
                    crate::common::Action::Swap { protocol, .. } |
                    crate::common::Action::Deposit { protocol, .. } |
                    crate::common::Action::Withdraw { protocol, .. } => {
                        protocols.push(protocol.clone());
                    }
                    crate::common::Action::Bridge { .. } |
                    crate::common::Action::Transfer { .. } => {
                        // Bridge and Transfer actions don't have protocols
                    }
                }
            }
            crate::common::Expr::Seq { e1, e2 } => {
                self.extract_protocols_recursive(e1, protocols);
                self.extract_protocols_recursive(e2, protocols);
            }
            crate::common::Expr::Parallel { exprs } => {
                for expr in exprs {
                    self.extract_protocols_recursive(expr, protocols);
                }
            }
            crate::common::Expr::OnChain { expr, .. } => {
                self.extract_protocols_recursive(expr, protocols);
            }
        }
    }
    
    /// Check if an expression contains parallel operations
    fn has_parallel_expr(&self, expr: &crate::common::Expr) -> bool {
        match expr {
            crate::common::Expr::Parallel { .. } => true,
            crate::common::Expr::Seq { e1, e2 } => {
                self.has_parallel_expr(e1) || self.has_parallel_expr(e2)
            }
            crate::common::Expr::OnChain { expr, .. } => {
                self.has_parallel_expr(expr)
            }
            _ => false,
        }
    }
    
    /// Assess risk factors for a bundle
    fn assess_risk_factors(&self, bundle: &Bundle, analysis: &BundleAnalysis) -> Vec<RiskFactor> {
        let mut risk_factors = Vec::new();
        
        // High complexity risk
        if analysis.action_count > 10 {
            risk_factors.push(RiskFactor::HighComplexity(0.3));
        }
        
        // Cross-chain risk
        if analysis.has_cross_chain {
            risk_factors.push(RiskFactor::CrossChainUnsafe(
                "Cross-chain operations detected".to_string()
            ));
        }
        
        // Gas risk for complex bundles
        if analysis.complexity_estimate.estimated_time_us > 1000 {
            risk_factors.push(RiskFactor::GasRisk(
                "High gas consumption estimated".to_string()
            ));
        }
        
        risk_factors
    }
    
    /// Calculate overall risk score from individual risk factors
    fn calculate_overall_risk(&self, risk_factors: &[RiskFactor]) -> f64 {
        if risk_factors.is_empty() {
            return 0.1; // Minimum risk
        }
        
        let base_risk = 0.2; // Base risk for unknown patterns
        let factor_risk: f64 = risk_factors.iter().map(|factor| {
            match factor {
                RiskFactor::HighComplexity(score) => *score,
                RiskFactor::CrossChainUnsafe(_) => 0.3,
                RiskFactor::GasRisk(_) => 0.2,
                RiskFactor::UnknownActions(_) => 0.4,
                _ => 0.1,
            }
        }).sum();
        
        (base_risk + factor_risk).min(1.0)
    }
}

impl StaticPatternLibrary {
    /// Load the static pattern library (placeholder for now)
    fn load() -> Result<Self, ValidationError> {
        // This will be implemented when we add pattern loading from maths/ folder
        Ok(Self {
            patterns: HashMap::new(),
            pattern_index: HashMap::new(),
            ordered_patterns: Vec::new(),
        })
    }
}

impl DynamicPatternCache {
    /// Create a new dynamic pattern cache
    fn new(capacity: usize) -> Self {
        Self {
            recent_matches: lru::LruCache::new(std::num::NonZeroUsize::new(capacity).unwrap()),
            negative_cache: std::collections::HashSet::new(),
            pattern_stats: HashMap::new(),
        }
    }
}

impl PerformanceMonitor {
    /// Create a new performance monitor
    fn new() -> Self {
        Self {
            total_analyses: 0,
            timing_checkpoints: Vec::new(),
            current_analysis_start: None,
        }
    }
}

impl AnalyzerConfig {
    /// Default configuration for development
    pub fn development() -> Self {
        Self {
            max_analysis_time_us: 5000, // 5ms for development
            cache_size: 100,
            enable_monitoring: true,
            partial_match_threshold: 0.7,
            risk_threshold: 0.5,
        }
    }
    
    /// Production configuration with tighter performance constraints
    pub fn production() -> Self {
        Self {
            max_analysis_time_us: 500, // 500μs for production
            cache_size: 1000,
            enable_monitoring: true,
            partial_match_threshold: 0.8,
            risk_threshold: 0.3,
        }
    }
}

impl Default for AnalyzerConfig {
    fn default() -> Self {
        Self::development()
    }
}

impl AnalysisContext {
    /// Create a new analysis context
    fn new(bundle: Bundle, bundle_hash: String, start_time: Instant) -> Self {
        Self {
            bundle,
            bundle_hash,
            start_time,
            checkpoints: Vec::new(),
            partial_results: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{Chain, Token, Protocol, Rational, Action, Expr};

    #[test]
    fn test_analyzer_engine_creation() {
        let analyzer = AnalyzerEngine::new();
        assert!(analyzer.is_ok());
    }

    #[test]
    fn test_bundle_analysis() {
        let analyzer = AnalyzerEngine::new().unwrap();
        
        let bundle = Bundle {
            name: "test_bundle".to_string(),
            start_chain: Chain::Polygon,
            expr: Expr::Action {
                action: Action::Swap {
                    amount_in: Rational::new(100, 1),
                    token_in: Token::USDC,
                    token_out: Token::WETH,
                    min_out: Rational::new(1, 2),
                    protocol: Protocol::UniswapV2,
                }
            },
            constraints: vec![],
        };
        
        let analysis = analyzer.analyze_bundle_properties(&bundle);
        assert_eq!(analysis.action_count, 1);
        assert_eq!(analysis.tokens_involved.len(), 2);
        assert_eq!(analysis.protocols_involved.len(), 1);
        assert!(!analysis.has_cross_chain);
        assert!(!analysis.has_parallel);
    }
}