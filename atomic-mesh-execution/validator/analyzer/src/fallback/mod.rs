//! Fallback system for graceful degradation
//! 
//! This module provides the tiered fallback system that enables
//! the analyzer to gracefully handle unknown patterns.

pub mod analysis_result;
pub mod result_builder;

pub use analysis_result::*;
pub use result_builder::ResultBuilder;