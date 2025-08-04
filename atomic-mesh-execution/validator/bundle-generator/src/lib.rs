//! Bundle Generator Module
//! 
//! This module is responsible for transforming mathematically verified patterns
//! into concrete, executable bundles ready for on-chain execution.

pub mod types;
pub mod error;
pub mod traits;
pub mod registry;
pub mod patterns;
pub mod generator;
pub mod builder;
pub mod analysis_result;
pub mod bundle_ext;

// Re-export main types
pub use types::{
    ExecutionBundle, ExecutionPlan, ExecutionStep, OperationType,
    GasConfig, ProfitConfig, ChainContracts, OptimizationHints,
    PatternParameters, ProtocolInfo, Address
};
pub use error::{BundleGeneratorError, Result};
pub use traits::PatternBundleGenerator;
pub use generator::BundleGenerator;
pub use builder::ExecutionBundleBuilder;
pub use analysis_result::{AnalysisResult, PatternMatch, PatternType};

/// Module version
pub const VERSION: &str = env!("CARGO_PKG_VERSION");