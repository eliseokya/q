//! Semantic validation module for mathematical property verification
//! 
//! This module implements Phase 2 of the analyzer build plan:
//! - Mathematical property verification via theorem application
//! - Pattern confidence scoring based on proof strength

pub mod theorem_engine;
pub mod proof_application;

pub use theorem_engine::{TheoremEngine, TheoremError};
pub use proof_application::{ProofApplicationEngine, SemanticValidator};