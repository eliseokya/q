//! Core traits for pattern bundle generation

use crate::types::{ExecutionBundle, PatternParameters};
use crate::error::Result;

/// Trait that all pattern-specific generators must implement
pub trait PatternBundleGenerator: Send + Sync {
    /// Generate an execution bundle from pattern parameters
    fn generate(&self, params: &PatternParameters) -> Result<ExecutionBundle>;
    
    /// Estimate gas for the pattern execution
    fn estimate_gas(&self, params: &PatternParameters) -> Result<u64>;
    
    /// Validate that the pattern is feasible to execute
    fn validate_feasibility(&self, params: &PatternParameters) -> Result<()>;
    
    /// Get the pattern ID this generator handles
    fn pattern_id(&self) -> &str;
}