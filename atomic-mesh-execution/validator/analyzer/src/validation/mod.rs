//! Constraint validation module for verifying bundle constraints

pub mod constraint_checker;

pub use constraint_checker::{ConstraintChecker, ConstraintValidationResult, ConstraintSeverity};