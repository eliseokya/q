//! Main analyzer engine for pattern matching against mathematical theorems
//! 
//! Purpose: Matches DSL Bundle expressions against pre-proven mathematical patterns
//! ensuring mathematical correctness and atomicity guarantees.

use crate::common::{
    Bundle, AnalysisResult, ProvenPattern, PatternCandidate, 
    ValidationError, RiskProfile, BundleAnalysis, ComplexityEstimate,
    ValidationRecommendation, RiskFactor, RiskRecommendation,
};

use crate::engine::{StaticPatternLibrary, DynamicPatternCache};
use crate::matching::{StructuralMatcher, AutomataMatchEngine};
use crate::validation::ConstraintChecker;
use crate::semantic::{SemanticValidator, TheoremEngine};
use crate::scoring::{ConfidenceCalculator, RiskAssessor};
use crate::fallback::ResultBuilder;
use crate::heuristics::{StructuralAnalyzer, SafetyHeuristics};
use std::time::{Duration, Instant};
use std::collections::HashMap;
use uuid::Uuid;

/// Configuration for the analyzer engine
#[derive(Debug, Clone)]
pub struct AnalyzerConfig {
    /// Maximum time allowed for analysis (microseconds) 
    pub max_analysis_time_us: u64,
    /// Whether to enable heuristic fallback for unknown patterns
    pub enable_heuristic_fallback: bool,
    /// Confidence threshold for pattern matches
    pub min_confidence_threshold: f64,
    /// Maximum number of patterns to consider
    pub max_patterns_to_check: usize,
}

impl Default for AnalyzerConfig {
    fn default() -> Self {
        Self {
            max_analysis_time_us: 500, // 500μs as per build plan
            enable_heuristic_fallback: true,
            min_confidence_threshold: 0.7,
            max_patterns_to_check: 100,
        }
    }
}

/// Performance tracking for analyzer operations
#[derive(Debug, Clone, Default)]
pub struct PerformanceMetrics {
    pub total_analysis_time_us: u64,
    pub pattern_matching_time_us: u64,
    pub constraint_validation_time_us: u64,
    pub semantic_validation_time_us: u64,
    pub patterns_checked: usize,
    pub cache_hits: usize,
    pub cache_misses: usize,
    pub structural_match_time_us: u64,
}

/// Main analyzer engine that orchestrates pattern matching
pub struct AnalyzerEngine {
    config: AnalyzerConfig,
    pattern_library: StaticPatternLibrary,
    pattern_cache: DynamicPatternCache,
    structural_matcher: StructuralMatcher,
    automata_engine: AutomataMatchEngine,
    constraint_checker: ConstraintChecker,
    semantic_validator: SemanticValidator,
    confidence_calculator: ConfidenceCalculator,
    risk_assessor: RiskAssessor,
    performance_metrics: PerformanceMetrics,
}

impl AnalyzerEngine {
    /// Create a new analyzer engine with default configuration
    pub fn new() -> Result<Self, ValidationError> {
        Self::with_config(AnalyzerConfig::default())
    }

    /// Create analyzer with custom configuration
    pub fn with_config(config: AnalyzerConfig) -> Result<Self, ValidationError> {
        let structural_matcher = StructuralMatcher::new();
        let automata_engine = AutomataMatchEngine::new();
        let constraint_checker = ConstraintChecker::new();
        let semantic_validator = SemanticValidator::new();
        let confidence_calculator = ConfidenceCalculator::new();
        let risk_assessor = RiskAssessor::new();
        
        Ok(Self {
            config,
            pattern_library: StaticPatternLibrary::load()
                .map_err(|e| ValidationError::PatternLoadError { 
                    details: format!("Failed to load pattern library: {}", e) 
                })?,
            pattern_cache: DynamicPatternCache::new(1000),
            structural_matcher,
            automata_engine,
            constraint_checker,
            semantic_validator,
            confidence_calculator,
            risk_assessor,
            performance_metrics: PerformanceMetrics::default(),
        })
    }

    /// Load patterns into the engine
    pub fn load_patterns(&mut self, patterns: Vec<ProvenPattern>) -> Result<(), ValidationError> {
        // Load patterns into automata engine
        self.automata_engine.load_patterns(&patterns)
            .map_err(|e| ValidationError::PatternLoadError { details: e })?;
        
        // Get all automata and load into structural matcher
        let automata = self.automata_engine.get_all_automata();
        self.structural_matcher.load_automata(automata);
        
        // Load patterns into pattern library
        self.pattern_library.load_patterns(patterns)
            .map_err(|e| ValidationError::PatternLoadError { 
                details: format!("Failed to load patterns into library: {}", e) 
            })?;
        
        Ok(())
    }

    /// Main analysis entry point - analyze a bundle against proven patterns
    pub fn analyze_bundle(&mut self, bundle: &Bundle) -> AnalysisResult {
        let start_time = Instant::now();
        
        // Create bundle hash for caching
        let bundle_hash = self.compute_bundle_hash(bundle);
        
        // Check cache first
        if let Some(cached_match) = self.pattern_cache.get(&bundle_hash) {
            self.performance_metrics.cache_hits += 1;
            return AnalysisResult::FullMatch {
                theorem_reference: cached_match.pattern_match.pattern.theorem_reference.clone(),
                confidence: cached_match.pattern_match.confidence_score,
                safety_guarantees: cached_match.pattern_match.pattern.safety_properties.clone(),
                gas_optimization_available: cached_match.pattern_match.pattern.gas_optimization_potential,
                execution_plan: format!("Cached: Execute pattern {}", cached_match.pattern_match.pattern.pattern_id),
            };
        }
        
        self.performance_metrics.cache_misses += 1;
        
        // Perform structural analysis
        let bundle_analysis = self.analyze_bundle_structure(bundle);
        
        // Try pattern matching with performance budget
        let result = self.match_patterns_with_timeout(bundle, &bundle_analysis, start_time);
        
        // Update performance metrics
        let elapsed = start_time.elapsed();
        self.performance_metrics.total_analysis_time_us = elapsed.as_micros() as u64;
        
        result
    }

    /// Pattern matching with strict timeout enforcement
    fn match_patterns_with_timeout(
        &mut self, 
        bundle: &Bundle, 
        bundle_analysis: &BundleAnalysis,
        start_time: Instant
    ) -> AnalysisResult {
        let timeout = Duration::from_micros(self.config.max_analysis_time_us);
        
        // Phase 1: Fast structural matching (200μs budget)
        let pattern_start = Instant::now();
        let pattern_candidates = self.structural_pattern_match(bundle);
        let pattern_time = pattern_start.elapsed();
        
        // Check timeout
        if start_time.elapsed() > timeout {
            return self.create_timeout_error(bundle_analysis);
        }
        
        self.performance_metrics.pattern_matching_time_us = pattern_time.as_micros() as u64;
        self.performance_metrics.patterns_checked = pattern_candidates.len();
        
        // Phase 2: Constraint validation (100μs budget)
        let constraint_start = Instant::now();
        let validated_candidates = self.filter_by_constraints(pattern_candidates, bundle);
        let constraint_time = constraint_start.elapsed();
        
        // Check timeout
        if start_time.elapsed() > timeout {
            return self.create_timeout_error(bundle_analysis);
        }
        
        self.performance_metrics.constraint_validation_time_us = constraint_time.as_micros() as u64;
        
        // Phase 3: Semantic validation (80μs budget)
        let semantic_start = Instant::now();
        let final_matches = self.apply_semantic_validation(&validated_candidates, bundle);
        let semantic_time = semantic_start.elapsed();
        
        self.performance_metrics.semantic_validation_time_us = semantic_time.as_micros() as u64;
        
        // Phase 4: Result generation (remaining budget)
        self.generate_final_result(final_matches, bundle_analysis, bundle)
    }

    /// Phase 1: Structural pattern matching
    fn structural_pattern_match(&mut self, bundle: &Bundle) -> Vec<PatternCandidate> {
        let start_time = Instant::now();
        
        // Use the real structural matcher
        let match_results = self.structural_matcher.match_bundle(bundle);
        
        // Convert match results to pattern candidates
        let patterns = self.pattern_library.get_all_patterns();
        let candidates = self.structural_matcher.results_to_candidates(match_results, &patterns);
        
        self.performance_metrics.structural_match_time_us = start_time.elapsed().as_micros() as u64;
        
        candidates
    }

    /// Phase 2: Constraint validation (100μs budget)
    fn filter_by_constraints(&mut self, candidates: Vec<PatternCandidate>, bundle: &Bundle) -> Vec<PatternCandidate> {
        let start_time = Instant::now();
        
        // Use the real constraint checker
        let validation_result = self.constraint_checker.validate_bundle(bundle);
        
        let mut validated_candidates = candidates;
        
        // If constraints are violated, filter out candidates or adjust confidence
        if !validation_result.is_valid {
            for candidate in &mut validated_candidates {
                // Reduce confidence based on constraint violations
                let severity_penalty = validation_result.violated_constraints.iter()
                    .map(|v| match v.severity {
                        crate::validation::ConstraintSeverity::Critical => 0.5,
                        crate::validation::ConstraintSeverity::Warning => 0.2,
                        crate::validation::ConstraintSeverity::Info => 0.1,
                    })
                    .fold(1.0, |acc, penalty| acc * (1.0 - penalty));
                
                candidate.confidence_score *= severity_penalty;
            }
        }
        
        self.performance_metrics.constraint_validation_time_us = start_time.elapsed().as_micros() as u64;
        
        validated_candidates
    }

    /// Apply semantic validation using mathematical theorems
    fn apply_semantic_validation(
        &self, 
        candidates: &[PatternCandidate], 
        bundle: &Bundle
    ) -> Vec<PatternCandidate> {
        // Apply semantic validation and confidence scoring to candidates
        candidates.iter()
            .map(|candidate| {
                // Apply semantic validation
                let validation_result = self.semantic_validator.validate(bundle, candidate);
                
                // Update confidence based on validation result
                match &validation_result {
                    AnalysisResult::FullMatch { safety_guarantees, .. } => {
                        let enhanced_candidate = self.confidence_calculator.enhance_pattern_candidate(
                            candidate.clone(),
                            true, // theorem verified
                            safety_guarantees.clone(),
                        );
                        Some(enhanced_candidate)
                    }
                    AnalysisResult::PartialMatch { validated_properties, .. } => {
                        let enhanced_candidate = self.confidence_calculator.enhance_pattern_candidate(
                            candidate.clone(),
                            false, // partial match only
                            validated_properties.clone(),
                        );
                        Some(enhanced_candidate)
                    }
                    _ => {
                        // For heuristic or reject results, filter out the candidate
                        None
                    }
                }
            })
            .filter_map(|c| c)
            .filter(|candidate| candidate.confidence_score >= self.config.min_confidence_threshold)
            .collect()
    }

    /// Generate the final analysis result using the new fallback system
    fn generate_final_result(
        &mut self,
        matches: Vec<PatternCandidate>,
        bundle_analysis: &BundleAnalysis,
        bundle: &Bundle
    ) -> AnalysisResult {
        // Create a result builder
        let mut builder = ResultBuilder::new();
        
        // Add pattern candidates
        builder = builder.with_pattern_candidates(matches.clone());
        
        // Perform theorem validation for candidates
        let theorem_engine = TheoremEngine::new();
        let mut theorem_results = HashMap::new();
        
        for candidate in &matches {
            let theorem_result = theorem_engine.apply_theorem(bundle, &candidate.pattern)
                .map_err(|e| e);
            theorem_results.insert(candidate.pattern.theorem_reference.clone(), theorem_result);
        }
        
        builder = builder.with_theorem_results(theorem_results);
        
        // If no full match, perform structural analysis
        if matches.is_empty() || matches.iter().all(|m| m.confidence_score < 0.95) {
            let structural_analyzer = StructuralAnalyzer::new();
            let structural_analysis = structural_analyzer.analyze_structure(bundle);
            
            // Add structural match information
            let similarity = if matches.is_empty() { 0.0 } else { matches[0].confidence_score };
            builder = builder.with_structural_match(
                structural_analysis.pattern_type.clone(),
                similarity
            );
            
            // Check for safety violations
            let safety_heuristics = SafetyHeuristics::new();
            let violations = safety_heuristics.check_safety_violations(&structural_analysis);
            
            for violation in violations {
                builder = builder.add_rejection_reason(violation);
            }
            
            // Add risk factors
            if structural_analysis.protocol_risks.unknown_protocol_count > 0 {
                builder = builder.add_risk_factor(
                    format!("{} unknown protocols detected", structural_analysis.protocol_risks.unknown_protocol_count)
                );
            }
            
            if structural_analysis.cross_chain_complexity.chain_count > 1 {
                builder = builder.add_risk_factor(
                    format!("Cross-chain execution across {} chains", structural_analysis.cross_chain_complexity.chain_count)
                );
            }
        }
        
        // Build the final result with tiered fallback
        let enhanced_result = builder.build();
        
        // Convert to old AnalysisResult format for compatibility
        self.convert_enhanced_result_to_legacy(enhanced_result, bundle_analysis)
    }

    /// Convert enhanced result to legacy format for compatibility
    fn convert_enhanced_result_to_legacy(
        &self,
        enhanced_result: crate::fallback::AnalysisResult,
        bundle_analysis: &BundleAnalysis
    ) -> AnalysisResult {
        match enhanced_result {
            crate::fallback::AnalysisResult::FullMatch { 
                theorem_reference, 
                confidence, 
                safety_guarantees, 
                gas_optimization_available,
                execution_plan,
                .. 
            } => {
                AnalysisResult::FullMatch {
                    theorem_reference,
                    confidence,
                    safety_guarantees,
                    gas_optimization_available,
                    execution_plan,
                }
            }
            crate::fallback::AnalysisResult::PartialMatch { 
                confidence,
                validated_properties,
                unverified_properties,
                matched_structure,
                .. 
            } => {
                AnalysisResult::PartialMatch {
                    theorem_reference: matched_structure,
                    confidence,
                    validated_properties,
                    missing_guarantees: unverified_properties,
                    recommendation: if confidence >= 0.7 {
                        ValidationRecommendation::ProceedWithCaution
                    } else {
                        ValidationRecommendation::RequireAdditionalValidation
                    },
                }
            }
            crate::fallback::AnalysisResult::Heuristic { 
                confidence,
                risk_assessment,
                pattern_type,
                manual_review_required,
                .. 
            } => {
                AnalysisResult::Heuristic {
                    risk_assessment: self.convert_risk_assessment_to_profile(&risk_assessment),
                    confidence,
                    detected_patterns: vec![pattern_type],
                    safety_warnings: risk_assessment.mitigation_strategies.clone(),
                    manual_review_required,
                    analysis_id: Uuid::new_v4(),
                }
            }
            crate::fallback::AnalysisResult::Reject { reasons, suggested_fixes, .. } => {
                AnalysisResult::Reject {
                    error: ValidationError::MalformedBundle {
                        details: reasons.into_iter().map(|r| r.to_string()).collect::<Vec<_>>().join("; "),
                    },
                    bundle_hash: "unknown".to_string(),
                    analyzed_properties: bundle_analysis.clone(),
                    suggested_fixes: suggested_fixes.into_iter().map(|f| f.description).collect(),
                    analysis_id: Uuid::new_v4(),

                }
            }
        }
    }
    
    /// Convert risk assessment to risk profile
    fn convert_risk_assessment_to_profile(&self, assessment: &crate::fallback::RiskAssessment) -> RiskProfile {
        let mut risk_factors = Vec::new();
        
        // Convert each risk factor from the assessment
        for (name, score) in &assessment.risk_factors {
            if name.contains("cross_chain") {
                risk_factors.push(RiskFactor::CrossChainUnsafe(
                    format!("Cross-chain risk detected (score: {:.2})", score)
                ));
            } else if name.contains("protocol") {
                risk_factors.push(RiskFactor::UnknownActions(vec![
                    format!("Unknown protocol risk: {:.2}", score)
                ]));
            } else if name.contains("timing") {
                risk_factors.push(RiskFactor::TimingRisk(
                    format!("Timing constraint risk: {:.2}", score)
                ));
            } else {
                risk_factors.push(RiskFactor::HighComplexity(*score));
            }
        }
        
        let overall_score = assessment.risk_factors.values().sum::<f64>() / 
                           assessment.risk_factors.len().max(1) as f64;
        
        let recommendation = match assessment.overall_risk {
            crate::fallback::RiskLevel::Low => RiskRecommendation::LowRisk,
            crate::fallback::RiskLevel::Medium => RiskRecommendation::MediumRisk,
            crate::fallback::RiskLevel::High => RiskRecommendation::HighRisk,
            crate::fallback::RiskLevel::Critical => RiskRecommendation::HighRisk, // Use HighRisk for Critical
        };
        
        RiskProfile {
            overall_score,
            risk_factors,
            confidence: assessment.confidence_in_assessment,
            recommendation,
        }
    }

    /// Placeholder: Structural matching score calculation
    fn structural_match_score(&self, _expr: &common::Expr, _pattern: &ProvenPattern) -> Option<f64> {
        // Now delegated to StructuralMatcher
        None
    }

    /// Placeholder: Bundle constraint validation
    fn check_bundle_constraints(&self, _bundle: &Bundle) -> bool {
        // Now delegated to ConstraintChecker
        true
    }



    /// Analyze bundle structure for metadata
    fn analyze_bundle_structure(&self, bundle: &Bundle) -> BundleAnalysis {
        BundleAnalysis {
            action_count: self.count_actions(&bundle.expr),
            chains_involved: self.extract_chains(&bundle.expr),
            tokens_involved: self.extract_tokens(&bundle.expr),
            protocols_involved: self.extract_protocols(&bundle.expr),
            complexity_estimate: ComplexityEstimate {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(1)".to_string(),
                estimated_time_us: 300,
                estimated_memory_bytes: 1024,
            },
            has_cross_chain: self.has_cross_chain_operations(&bundle.expr),
            has_parallel: self.has_parallel_operations(&bundle.expr),
        }
    }

    /// Helper functions for bundle analysis
    fn count_actions(&self, expr: &common::Expr) -> usize {
        match expr {
            common::Expr::Action { .. } => 1,
            common::Expr::Seq { first, second } => self.count_actions(first) + self.count_actions(second),
            common::Expr::Parallel { exprs } => exprs.iter().map(|e| self.count_actions(e)).sum(),
            common::Expr::OnChain { expr, .. } => self.count_actions(expr),
        }
    }

    fn extract_chains(&self, expr: &common::Expr) -> Vec<common::Chain> {
        match expr {
            common::Expr::OnChain { chain, expr } => {
                let mut chains = vec![chain.clone()];
                chains.extend(self.extract_chains(expr));
                chains
            },
            common::Expr::Action { action } => {
                match action {
                    common::Action::Bridge { chain, .. } => vec![chain.clone()],
                    _ => vec![],
                }
            },
            common::Expr::Seq { first, second } => {
                let mut chains = self.extract_chains(first);
                chains.extend(self.extract_chains(second));
                chains
            },
            common::Expr::Parallel { exprs } => {
                exprs.iter().flat_map(|e| self.extract_chains(e)).collect()
            },
        }
    }

    fn extract_tokens(&self, expr: &common::Expr) -> Vec<common::Token> {
        match expr {
            common::Expr::Action { action } => {
                match action {
                    common::Action::Borrow { token, .. } | 
                    common::Action::Repay { token, .. } |
                    common::Action::Deposit { token, .. } |
                    common::Action::Withdraw { token, .. } => vec![token.clone()],
                    common::Action::Swap { token_in, token_out, .. } => vec![token_in.clone(), token_out.clone()],
                    common::Action::Bridge { token, .. } => vec![token.clone()],
                }
            },
            common::Expr::Seq { first, second } => {
                let mut tokens = self.extract_tokens(first);
                tokens.extend(self.extract_tokens(second));
                tokens
            },
            common::Expr::Parallel { exprs } => {
                exprs.iter().flat_map(|e| self.extract_tokens(e)).collect()
            },
            common::Expr::OnChain { expr, .. } => self.extract_tokens(expr),
        }
    }

    fn extract_protocols(&self, expr: &common::Expr) -> Vec<common::Protocol> {
        match expr {
            common::Expr::Action { action } => {
                match action {
                    common::Action::Borrow { protocol, .. } |
                    common::Action::Repay { protocol, .. } |
                    common::Action::Swap { protocol, .. } |
                    common::Action::Deposit { protocol, .. } |
                    common::Action::Withdraw { protocol, .. } => vec![protocol.clone()],
                    _ => vec![],
                }
            },
            common::Expr::Seq { first, second } => {
                let mut protocols = self.extract_protocols(first);
                protocols.extend(self.extract_protocols(second));
                protocols
            },
            common::Expr::Parallel { exprs } => {
                exprs.iter().flat_map(|e| self.extract_protocols(e)).collect()
            },
            common::Expr::OnChain { expr, .. } => self.extract_protocols(expr),
        }
    }

    fn has_cross_chain_operations(&self, expr: &common::Expr) -> bool {
        match expr {
            common::Expr::Action { action } => matches!(action, common::Action::Bridge { .. }),
            common::Expr::Seq { first, second } => 
                self.has_cross_chain_operations(first) || self.has_cross_chain_operations(second),
            common::Expr::Parallel { exprs } => 
                exprs.iter().any(|e| self.has_cross_chain_operations(e)),
            common::Expr::OnChain { expr, .. } => self.has_cross_chain_operations(expr),
        }
    }

    fn has_parallel_operations(&self, expr: &common::Expr) -> bool {
        matches!(expr, common::Expr::Parallel { .. })
    }

    /// Utility functions
    fn compute_bundle_hash(&self, bundle: &Bundle) -> String {
        format!("{:?}", bundle) // Simple hash - TODO: implement proper hashing
    }

    fn validate_pattern(&self, _pattern: &ProvenPattern) -> Result<(), ValidationError> {
        // TODO: Validate pattern structure
        Ok(())
    }

    fn create_timeout_error(&self, bundle_analysis: &BundleAnalysis) -> AnalysisResult {
        AnalysisResult::Reject {
            error: ValidationError::PerformanceTimeout { 
                timeout_ms: self.config.max_analysis_time_us / 1000 
            },
            bundle_hash: "timeout".to_string(),
            analyzed_properties: bundle_analysis.clone(),
            suggested_fixes: vec![
                "Simplify bundle structure".to_string(),
                "Reduce number of operations".to_string(),
            ],
            analysis_id: Uuid::new_v4(),
        }
    }

    fn create_heuristic_result(&self, bundle_analysis: &BundleAnalysis) -> AnalysisResult {
        let risk_score = if bundle_analysis.has_cross_chain { 0.6 } else { 0.3 };
        
        AnalysisResult::heuristic(
            RiskProfile::new(risk_score, vec![], 0.5),
            0.5,
            vec!["Unknown pattern detected".to_string()],
            vec!["Manual review recommended".to_string()],
            true,
        )
    }
    
    fn create_heuristic_result_with_risk(
        &self, 
        _bundle_analysis: &BundleAnalysis,
        risk_profile: RiskProfile,
        confidence: f64
    ) -> AnalysisResult {
        AnalysisResult::heuristic(
            risk_profile,
            confidence,
            vec!["Pattern analyzed using risk assessment".to_string()],
            vec!["Review risk factors before execution".to_string()],
            true, // Always require manual review for unknown patterns
        )
    }
    
    fn calculate_pattern_similarity(&self, bundle: &Bundle) -> f64 {
        // Get known pattern signatures from the pattern library
        let known_patterns: Vec<String> = self.pattern_library.get_all_patterns()
            .iter()
            .map(|p| p.pattern_id.clone())
            .collect();
        
        // Use risk assessor to calculate similarity
        self.risk_assessor.calculate_pattern_similarity(bundle, &known_patterns)
    }

    fn create_rejection_result(&self, bundle_analysis: &BundleAnalysis) -> AnalysisResult {
        AnalysisResult::reject(
            ValidationError::UnknownPattern,
            "unknown".to_string(),
            bundle_analysis.clone(),
            vec!["Check pattern library for similar patterns".to_string()],
        )
    }

    /// Get performance metrics
    pub fn get_metrics(&self) -> &PerformanceMetrics {
        &self.performance_metrics
    }

    /// Clear performance metrics
    pub fn reset_metrics(&mut self) {
        self.performance_metrics = PerformanceMetrics::default();
    }
}