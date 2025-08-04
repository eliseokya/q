//! Pattern discovery system for identifying new composite patterns
//! 
//! This module analyzes successful pattern matches to discover new
//! composite patterns that can be added to the library.

pub mod pattern_composer;
pub mod structure_analyzer;

pub use pattern_composer::{PatternComposer, CompositePattern};
pub use structure_analyzer::{StructureAnalyzer, PatternStructure};