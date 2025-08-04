//! Performance timing monitor for tracking operation durations
//!
//! This module provides microsecond-precision timing for analyzer operations
//! to help identify performance bottlenecks and ensure we meet timing targets.

use std::time::{Duration, Instant};
use std::collections::HashMap;

/// Tracks timing for different analyzer operations
#[derive(Debug, Clone)]
pub struct TimingMonitor {
    /// Start time of the overall analysis
    start_time: Instant,
    /// Individual operation timings
    operation_times: HashMap<String, Duration>,
    /// Current operation being timed
    current_operation: Option<(String, Instant)>,
}

/// Timing results for a complete analysis
#[derive(Debug, Clone)]
pub struct OperationTiming {
    pub total_duration_us: u64,
    pub input_parsing_us: u64,
    pub pattern_loading_us: u64,
    pub structural_matching_us: u64,
    pub constraint_validation_us: u64,
    pub semantic_validation_us: u64,
    pub result_formatting_us: u64,
    pub other_operations_us: u64,
}

impl TimingMonitor {
    /// Create a new timing monitor
    pub fn new() -> Self {
        Self {
            start_time: Instant::now(),
            operation_times: HashMap::new(),
            current_operation: None,
        }
    }

    /// Start timing an operation
    pub fn start_operation(&mut self, operation: &str) {
        // If there's a current operation, finish it first
        if let Some((op_name, op_start)) = self.current_operation.take() {
            let duration = op_start.elapsed();
            self.operation_times.insert(op_name, duration);
        }
        
        // Start the new operation
        self.current_operation = Some((operation.to_string(), Instant::now()));
    }

    /// Finish the current operation
    pub fn finish_operation(&mut self) {
        if let Some((op_name, op_start)) = self.current_operation.take() {
            let duration = op_start.elapsed();
            self.operation_times.insert(op_name, duration);
        }
    }

    /// Get the total elapsed time
    pub fn total_elapsed(&self) -> Duration {
        self.start_time.elapsed()
    }

    /// Get timing results
    pub fn get_timing_results(&mut self) -> OperationTiming {
        // Finish any pending operation
        self.finish_operation();
        
        let total = self.total_elapsed();
        
        // Extract specific operation times
        let input_parsing = self.operation_times.get("input_parsing")
            .map(|d| d.as_micros() as u64)
            .unwrap_or(0);
            
        let pattern_loading = self.operation_times.get("pattern_loading")
            .map(|d| d.as_micros() as u64)
            .unwrap_or(0);
            
        let structural_matching = self.operation_times.get("structural_matching")
            .map(|d| d.as_micros() as u64)
            .unwrap_or(0);
            
        let constraint_validation = self.operation_times.get("constraint_validation")
            .map(|d| d.as_micros() as u64)
            .unwrap_or(0);
            
        let semantic_validation = self.operation_times.get("semantic_validation")
            .map(|d| d.as_micros() as u64)
            .unwrap_or(0);
            
        let result_formatting = self.operation_times.get("result_formatting")
            .map(|d| d.as_micros() as u64)
            .unwrap_or(0);
        
        // Calculate other operations
        let accounted_time = input_parsing + pattern_loading + structural_matching +
                           constraint_validation + semantic_validation + result_formatting;
        let total_us = total.as_micros() as u64;
        let other_operations = if total_us > accounted_time {
            total_us - accounted_time
        } else {
            0
        };
        
        OperationTiming {
            total_duration_us: total_us,
            input_parsing_us: input_parsing,
            pattern_loading_us: pattern_loading,
            structural_matching_us: structural_matching,
            constraint_validation_us: constraint_validation,
            semantic_validation_us: semantic_validation,
            result_formatting_us: result_formatting,
            other_operations_us: other_operations,
        }
    }

    /// Reset the monitor for a new analysis
    pub fn reset(&mut self) {
        self.start_time = Instant::now();
        self.operation_times.clear();
        self.current_operation = None;
    }
}

impl Default for TimingMonitor {
    fn default() -> Self {
        Self::new()
    }
}

impl OperationTiming {
    /// Check if timing meets performance budget
    pub fn meets_budget(&self, budget: &super::PerformanceBudget) -> bool {
        self.total_duration_us <= budget.total_budget_us &&
        self.input_parsing_us <= budget.input_parsing_us &&
        self.pattern_loading_us <= budget.pattern_loading_us &&
        self.structural_matching_us <= budget.structural_matching_us &&
        self.constraint_validation_us <= budget.constraint_validation_us &&
        self.semantic_validation_us <= budget.semantic_validation_us &&
        self.result_formatting_us <= budget.result_formatting_us
    }

    /// Get a human-readable performance report
    pub fn performance_report(&self) -> String {
        format!(
            "Performance Report:\n\
             ├─ Total Duration: {}μs\n\
             ├─ Input Parsing: {}μs\n\
             ├─ Pattern Loading: {}μs\n\
             ├─ Structural Matching: {}μs\n\
             ├─ Constraint Validation: {}μs\n\
             ├─ Semantic Validation: {}μs\n\
             ├─ Result Formatting: {}μs\n\
             └─ Other Operations: {}μs",
            self.total_duration_us,
            self.input_parsing_us,
            self.pattern_loading_us,
            self.structural_matching_us,
            self.constraint_validation_us,
            self.semantic_validation_us,
            self.result_formatting_us,
            self.other_operations_us
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;
    use std::time::Duration;

    #[test]
    fn test_timing_monitor_creation() {
        let monitor = TimingMonitor::new();
        assert!(monitor.operation_times.is_empty());
        assert!(monitor.current_operation.is_none());
    }

    #[test]
    fn test_operation_timing() {
        let mut monitor = TimingMonitor::new();
        
        monitor.start_operation("test_op");
        thread::sleep(Duration::from_millis(1));
        monitor.finish_operation();
        
        let results = monitor.get_timing_results();
        assert!(results.total_duration_us > 0);
    }

    #[test]
    fn test_multiple_operations() {
        let mut monitor = TimingMonitor::new();
        
        monitor.start_operation("input_parsing");
        thread::sleep(Duration::from_micros(10));
        
        monitor.start_operation("pattern_loading");
        thread::sleep(Duration::from_micros(10));
        
        monitor.start_operation("structural_matching");
        thread::sleep(Duration::from_micros(10));
        
        let results = monitor.get_timing_results();
        assert!(results.input_parsing_us > 0);
        assert!(results.pattern_loading_us > 0);
        assert!(results.structural_matching_us > 0);
    }
}