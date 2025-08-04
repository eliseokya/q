//! Error types for bundle generator

pub use crate::types::{BundleGeneratorError, BundleResult};

/// Type alias for standard Result using our error type
pub type Result<T> = std::result::Result<T, BundleGeneratorError>;