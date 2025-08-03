//! Analyzer engine module for pattern matching and theorem validation

pub mod analyzer_engine;
pub mod pattern_library;
pub mod cache;

// Re-export main engine types
pub use analyzer_engine::{AnalyzerEngine, AnalyzerConfig};
pub use pattern_library::{StaticPatternLibrary, PatternLibraryError};
pub use cache::{DynamicPatternCache, CacheEntry};