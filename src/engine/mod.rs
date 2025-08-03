//! Analyzer engine module
//! 
//! Contains the main analyzer engine and supporting components for
//! high-performance pattern matching and analysis.

pub mod analyzer_engine;

// Re-export main types
pub use analyzer_engine::{
    AnalyzerEngine, AnalyzerConfig, StaticPatternLibrary, DynamicPatternCache,
    PerformanceMonitor, PatternType, AnalysisContext,
};