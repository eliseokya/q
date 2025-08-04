//! Pattern confidence scoring module
//! 
//! This module implements the confidence calculation system for pattern matches:
//! - Mathematical confidence scoring based on proof strength
//! - Risk-based assessment for unknown patterns

pub mod confidence_calculator;
pub mod risk_assessor;

pub use confidence_calculator::{ConfidenceCalculator, ConfidenceConfig};
pub use risk_assessor::RiskAssessor;