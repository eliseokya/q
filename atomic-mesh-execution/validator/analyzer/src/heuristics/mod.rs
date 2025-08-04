//! Heuristic analysis for patterns without formal proofs
//! 
//! This module provides structural and safety heuristics to analyze
//! bundles when mathematical proofs are not available.

pub mod structural_analyzer;
pub mod safety_heuristics;

pub use structural_analyzer::{StructuralAnalyzer, StructuralAnalysis};
pub use safety_heuristics::{SafetyHeuristics, ExtendedSafetyChecks};