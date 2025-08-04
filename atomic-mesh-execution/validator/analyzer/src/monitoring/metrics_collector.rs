//! Metrics collection for production monitoring
//!
//! This module collects and aggregates performance metrics for the analyzer
//! to enable production monitoring and observability.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use crate::fallback::RejectionReason;
use crate::performance::OperationTiming;

/// Aggregated metrics for analyzer performance
#[derive(Debug, Clone)]
pub struct AnalysisMetrics {
    /// Total number of analyses performed
    pub total_analyses: u64,
    /// Number of successful analyses
    pub successful_analyses: u64,
    /// Number of failed analyses
    pub failed_analyses: u64,
    
    /// Pattern match statistics
    pub full_matches: u64,
    pub partial_matches: u64,
    pub heuristic_matches: u64,
    pub rejections: u64,
    
    /// Timing statistics (in microseconds)
    pub timing_p50: u64,
    pub timing_p95: u64,
    pub timing_p99: u64,
    pub timing_max: u64,
    
    /// Error statistics
    pub rejection_reasons: HashMap<String, u64>,
    
    /// Pattern usage statistics
    pub pattern_usage: HashMap<String, u64>,
}

/// Collects and aggregates analyzer metrics
pub struct MetricsCollector {
    metrics: Arc<Mutex<InternalMetrics>>,
}

#[derive(Debug)]
struct InternalMetrics {
    total_analyses: u64,
    successful_analyses: u64,
    failed_analyses: u64,
    
    full_matches: u64,
    partial_matches: u64,
    heuristic_matches: u64,
    rejections: u64,
    
    // Store all timings for percentile calculation
    timings: Vec<u64>,
    max_timing_samples: usize,
    
    rejection_reasons: HashMap<String, u64>,
    pattern_usage: HashMap<String, u64>,
}

impl MetricsCollector {
    /// Create a new metrics collector
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(Mutex::new(InternalMetrics {
                total_analyses: 0,
                successful_analyses: 0,
                failed_analyses: 0,
                full_matches: 0,
                partial_matches: 0,
                heuristic_matches: 0,
                rejections: 0,
                timings: Vec::new(),
                max_timing_samples: 10000, // Keep last 10k samples
                rejection_reasons: HashMap::new(),
                pattern_usage: HashMap::new(),
            })),
        }
    }

    /// Record a successful analysis
    pub fn record_success(&self, result_type: &str, timing: &OperationTiming, pattern_id: Option<&str>) {
        let mut metrics = self.metrics.lock().unwrap();
        
        metrics.total_analyses += 1;
        metrics.successful_analyses += 1;
        
        // Record result type
        match result_type {
            "FullMatch" => metrics.full_matches += 1,
            "PartialMatch" => metrics.partial_matches += 1,
            "Heuristic" => metrics.heuristic_matches += 1,
            _ => {}
        }
        
        // Record timing
        metrics.timings.push(timing.total_duration_us);
        if metrics.timings.len() > metrics.max_timing_samples {
            metrics.timings.remove(0);
        }
        
        // Record pattern usage
        if let Some(pattern) = pattern_id {
            *metrics.pattern_usage.entry(pattern.to_string()).or_insert(0) += 1;
        }
    }

    /// Record a failed analysis
    pub fn record_failure(&self, reason: &RejectionReason, timing: &OperationTiming) {
        let mut metrics = self.metrics.lock().unwrap();
        
        metrics.total_analyses += 1;
        metrics.failed_analyses += 1;
        metrics.rejections += 1;
        
        // Record timing even for failures
        metrics.timings.push(timing.total_duration_us);
        if metrics.timings.len() > metrics.max_timing_samples {
            metrics.timings.remove(0);
        }
        
        // Record rejection reason
        let reason_str = match reason {
            RejectionReason::MalformedStructure { .. } => "MalformedStructure",
            RejectionReason::SafetyViolation { .. } => "SafetyViolation",
            RejectionReason::ConstraintViolation { .. } => "ConstraintViolation",
            RejectionReason::InsufficientLiquidity { .. } => "InsufficientLiquidity",
            RejectionReason::UnsupportedProtocol { .. } => "UnsupportedProtocol",
            RejectionReason::TimingConflict { .. } => "TimingConflict",
            RejectionReason::HighRiskPattern { .. } => "HighRiskPattern",
        };
        
        *metrics.rejection_reasons.entry(reason_str.to_string()).or_insert(0) += 1;
    }

    /// Get current metrics snapshot
    pub fn get_metrics(&self) -> AnalysisMetrics {
        let metrics = self.metrics.lock().unwrap();
        
        // Calculate percentiles
        let mut sorted_timings = metrics.timings.clone();
        sorted_timings.sort_unstable();
        
        let p50 = calculate_percentile(&sorted_timings, 50);
        let p95 = calculate_percentile(&sorted_timings, 95);
        let p99 = calculate_percentile(&sorted_timings, 99);
        let max = sorted_timings.last().copied().unwrap_or(0);
        
        AnalysisMetrics {
            total_analyses: metrics.total_analyses,
            successful_analyses: metrics.successful_analyses,
            failed_analyses: metrics.failed_analyses,
            full_matches: metrics.full_matches,
            partial_matches: metrics.partial_matches,
            heuristic_matches: metrics.heuristic_matches,
            rejections: metrics.rejections,
            timing_p50: p50,
            timing_p95: p95,
            timing_p99: p99,
            timing_max: max,
            rejection_reasons: metrics.rejection_reasons.clone(),
            pattern_usage: metrics.pattern_usage.clone(),
        }
    }

    /// Reset all metrics
    pub fn reset(&self) {
        let mut metrics = self.metrics.lock().unwrap();
        metrics.total_analyses = 0;
        metrics.successful_analyses = 0;
        metrics.failed_analyses = 0;
        metrics.full_matches = 0;
        metrics.partial_matches = 0;
        metrics.heuristic_matches = 0;
        metrics.rejections = 0;
        metrics.timings.clear();
        metrics.rejection_reasons.clear();
        metrics.pattern_usage.clear();
    }

    /// Get metrics report as string
    pub fn get_report(&self) -> String {
        let metrics = self.get_metrics();
        
        format!(
            "Analyzer Metrics Report\n\
             =======================\n\
             Total Analyses: {}\n\
             Successful: {} ({:.1}%)\n\
             Failed: {} ({:.1}%)\n\
             \n\
             Result Types:\n\
             - Full Matches: {} ({:.1}%)\n\
             - Partial Matches: {} ({:.1}%)\n\
             - Heuristic: {} ({:.1}%)\n\
             - Rejections: {} ({:.1}%)\n\
             \n\
             Performance (μs):\n\
             - P50: {}\n\
             - P95: {}\n\
             - P99: {}\n\
             - Max: {}\n\
             \n\
             Top Rejection Reasons:\n\
             {}\n\
             \n\
             Top Used Patterns:\n\
             {}",
            metrics.total_analyses,
            metrics.successful_analyses,
            percentage(metrics.successful_analyses, metrics.total_analyses),
            metrics.failed_analyses,
            percentage(metrics.failed_analyses, metrics.total_analyses),
            metrics.full_matches,
            percentage(metrics.full_matches, metrics.total_analyses),
            metrics.partial_matches,
            percentage(metrics.partial_matches, metrics.total_analyses),
            metrics.heuristic_matches,
            percentage(metrics.heuristic_matches, metrics.total_analyses),
            metrics.rejections,
            percentage(metrics.rejections, metrics.total_analyses),
            metrics.timing_p50,
            metrics.timing_p95,
            metrics.timing_p99,
            metrics.timing_max,
            format_top_items(&metrics.rejection_reasons, 5),
            format_top_items(&metrics.pattern_usage, 5)
        )
    }
}

impl Default for MetricsCollector {
    fn default() -> Self {
        Self::new()
    }
}

fn calculate_percentile(sorted_values: &[u64], percentile: usize) -> u64 {
    if sorted_values.is_empty() {
        return 0;
    }
    
    let index = (sorted_values.len() * percentile) / 100;
    let index = index.saturating_sub(1);
    sorted_values[index]
}

fn percentage(part: u64, total: u64) -> f64 {
    if total == 0 {
        0.0
    } else {
        (part as f64 / total as f64) * 100.0
    }
}

fn format_top_items(items: &HashMap<String, u64>, top_n: usize) -> String {
    let mut sorted: Vec<_> = items.iter().collect();
    sorted.sort_by_key(|(_, count)| std::cmp::Reverse(**count));
    
    sorted.iter()
        .take(top_n)
        .map(|(name, count)| format!("- {}: {}", name, count))
        .collect::<Vec<_>>()
        .join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::performance::OperationTiming;

    #[test]
    fn test_metrics_collector() {
        let collector = MetricsCollector::new();
        
        let timing = OperationTiming {
            total_duration_us: 450,
            input_parsing_us: 40,
            pattern_loading_us: 15,
            structural_matching_us: 180,
            constraint_validation_us: 90,
            semantic_validation_us: 75,
            result_formatting_us: 40,
            other_operations_us: 10,
        };
        
        // Record some successes
        collector.record_success("FullMatch", &timing, Some("flash_loan"));
        collector.record_success("PartialMatch", &timing, None);
        
        let metrics = collector.get_metrics();
        assert_eq!(metrics.total_analyses, 2);
        assert_eq!(metrics.successful_analyses, 2);
        assert_eq!(metrics.full_matches, 1);
        assert_eq!(metrics.partial_matches, 1);
    }

    #[test]
    fn test_percentile_calculation() {
        let values = vec![100, 200, 300, 400, 500, 600, 700, 800, 900, 1000];
        assert_eq!(calculate_percentile(&values, 50), 500);
        assert_eq!(calculate_percentile(&values, 95), 900);
        assert_eq!(calculate_percentile(&values, 99), 900);
    }
}