//! Pattern matching module for structural matching against DSL expressions

pub mod structural_matcher;
pub mod automata;

pub use structural_matcher::{StructuralMatcher, MatchResult};
pub use automata::AutomataMatchEngine;