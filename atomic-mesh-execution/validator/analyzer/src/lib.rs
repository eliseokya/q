//! Analyzer module for the Atomic Mesh VM Validator
//! 
//! Pattern matches DSL bundles against mathematically proven patterns.

pub mod common;
pub mod pattern_scanner;
pub mod pattern_compiler;
pub mod matching;
pub mod validation;
pub mod semantic;
pub mod scoring;
pub mod hotreload;
pub mod discovery;
pub mod fallback;
pub mod heuristics;
pub mod engine;
pub mod performance;
pub mod monitoring;
pub mod integration;

// Re-export main types
pub use common::*;
pub use engine::AnalyzerEngine;
pub use fallback::AnalysisResult;

// Re-export performance types
pub use performance::{TimingMonitor, OperationTiming, PerformanceBudget, BudgetEnforcer};

// Re-export monitoring types  
pub use monitoring::{MetricsCollector, AnalysisMetrics, HealthChecker, HealthStatus};

// Re-export integration types
pub use integration::{CompilerInterface, CompilerMessage, PipelineManager, PipelineConfig, PipelineBuilder, PipelineError};
