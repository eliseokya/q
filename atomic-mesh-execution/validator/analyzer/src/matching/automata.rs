//! Automata match engine for managing and executing pattern matching
//!
//! This module coordinates multiple finite automata for efficient
//! parallel pattern matching.

use crate::pattern_compiler::{FiniteAutomaton, AutomataGenerator};
use crate::common::ProvenPattern;
use std::collections::HashMap;
use std::sync::Arc;
use parking_lot::RwLock;

/// Engine for managing and executing automata-based pattern matching
pub struct AutomataMatchEngine {
    /// All loaded automata indexed by pattern ID
    automata: Arc<RwLock<HashMap<String, FiniteAutomaton>>>,
    /// Automata generator for creating new patterns
    generator: AutomataGenerator,
    /// Performance tracking
    match_count: Arc<RwLock<usize>>,
}

impl AutomataMatchEngine {
    pub fn new() -> Self {
        Self {
            automata: Arc::new(RwLock::new(HashMap::new())),
            generator: AutomataGenerator::new(),
            match_count: Arc::new(RwLock::new(0)),
        }
    }

    /// Load automata from proven patterns
    pub fn load_patterns(&mut self, patterns: &[ProvenPattern]) -> Result<usize, String> {
        let mut loaded = 0;
        let mut automata = self.automata.write();

        for pattern in patterns {
            match self.generator.generate_from_regex(&pattern.pattern_id, &pattern.structure_regex) {
                Ok(automaton) => {
                    automata.insert(pattern.pattern_id.clone(), automaton.clone());
                    loaded += 1;
                }
                Err(e) => {
                    eprintln!("Failed to generate automaton for pattern {}: {}", pattern.pattern_id, e);
                }
            }
        }

        Ok(loaded)
    }

    /// Get a specific automaton by pattern ID
    pub fn get_automaton(&self, pattern_id: &str) -> Option<FiniteAutomaton> {
        self.automata.read().get(pattern_id).cloned()
    }

    /// Get all loaded automata
    pub fn get_all_automata(&self) -> HashMap<String, FiniteAutomaton> {
        self.automata.read().clone()
    }

    /// Add a new automaton at runtime
    pub fn add_automaton(&mut self, pattern_id: String, automaton: FiniteAutomaton) {
        self.automata.write().insert(pattern_id, automaton);
    }

    /// Remove an automaton
    pub fn remove_automaton(&mut self, pattern_id: &str) -> Option<FiniteAutomaton> {
        self.automata.write().remove(pattern_id)
    }

    /// Clear all automata
    pub fn clear(&mut self) {
        self.automata.write().clear();
        *self.match_count.write() = 0;
    }

    /// Get the number of loaded automata
    pub fn pattern_count(&self) -> usize {
        self.automata.read().len()
    }

    /// Increment match counter
    pub fn record_match(&self) {
        *self.match_count.write() += 1;
    }

    /// Get match statistics
    pub fn get_match_count(&self) -> usize {
        *self.match_count.read()
    }

    /// Merge multiple engines (useful for hot-reloading)
    pub fn merge(&mut self, other: AutomataMatchEngine) {
        let other_automata = other.automata.read();
        let mut our_automata = self.automata.write();
        
        for (pattern_id, automaton) in other_automata.iter() {
            our_automata.insert(pattern_id.clone(), automaton.clone());
        }
    }

    /// Create a merged automaton for even faster matching
    pub fn create_merged_automaton(&self) -> Option<FiniteAutomaton> {
        let automata = self.automata.read();
        if automata.is_empty() {
            return None;
        }

        let all_automata: Vec<FiniteAutomaton> = automata.values().cloned().collect();
        Some(self.generator.merge_automata(all_automata))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{SafetyProperty, PatternTemplate};
    use std::path::PathBuf;

    #[test]
    fn test_engine_operations() {
        let mut engine = AutomataMatchEngine::new();
        
        // Create test patterns
        let patterns = vec![
            ProvenPattern {
                pattern_id: "test1".to_string(),
                pattern_template: PatternTemplate::FlashLoan,
                theorem_reference: "theorem1".to_string(),
                theorem_file: PathBuf::from("test.lean"),
                theorem_line: 10,
                safety_properties: vec![SafetyProperty::Atomicity],
                preconditions: vec![],
                structure_regex: r"borrow.*repay".to_string(),
                confidence_threshold: 0.9,
                gas_optimization_potential: false,
            },
            ProvenPattern {
                pattern_id: "test2".to_string(),
                pattern_template: PatternTemplate::CrossChainArbitrage,
                theorem_reference: "theorem2".to_string(),
                theorem_file: PathBuf::from("test.lean"),
                theorem_line: 20,
                safety_properties: vec![SafetyProperty::CrossChainConsistency],
                preconditions: vec![],
                structure_regex: r"bridge.*swap".to_string(),
                confidence_threshold: 0.85,
                gas_optimization_potential: true,
            },
        ];

        // Load patterns
        let loaded = engine.load_patterns(&patterns).unwrap();
        assert_eq!(loaded, 2);
        assert_eq!(engine.pattern_count(), 2);

        // Test retrieval
        assert!(engine.get_automaton("test1").is_some());
        assert!(engine.get_automaton("test2").is_some());
        assert!(engine.get_automaton("nonexistent").is_none());

        // Test removal
        assert!(engine.remove_automaton("test1").is_some());
        assert_eq!(engine.pattern_count(), 1);

        // Test clear
        engine.clear();
        assert_eq!(engine.pattern_count(), 0);
    }
}