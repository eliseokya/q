//! Finite automata generator for O(1) pattern matching
//!
//! This module generates finite automata from patterns to enable
//! ultra-fast structural matching.

use std::collections::{HashMap, HashSet, VecDeque};
use regex::Regex;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AutomataError {
    #[error("Invalid regex pattern: {pattern}")]
    InvalidPattern { pattern: String },
    #[error("Automaton construction failed: {details}")]
    ConstructionError { details: String },
}

/// State in the finite automaton
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct State {
    id: usize,
    is_final: bool,
    pattern_id: Option<String>,
}

/// Transition in the finite automaton
#[derive(Debug, Clone)]
pub struct Transition {
    from_state: usize,
    to_state: usize,
    condition: TransitionCondition,
}

/// Conditions for state transitions
#[derive(Debug, Clone, PartialEq)]
pub enum TransitionCondition {
    /// Match a specific action type
    Action(String),
    /// Match any action
    AnyAction,
    /// Match a sequence operator
    Sequence,
    /// Match a parallel operator
    Parallel,
    /// Match a specific token
    Token(String),
    /// Match a specific protocol
    Protocol(String),
    /// Epsilon transition (no input consumed)
    Epsilon,
}

/// Finite automaton for pattern matching
#[derive(Debug)]
pub struct FiniteAutomaton {
    states: HashMap<usize, State>,
    transitions: Vec<Transition>,
    start_state: usize,
    current_state: usize,
    pattern_mappings: HashMap<usize, String>,
}

impl FiniteAutomaton {
    /// Create a new automaton with a start state
    pub fn new() -> Self {
        let start_state = State {
            id: 0,
            is_final: false,
            pattern_id: None,
        };
        
        let mut states = HashMap::new();
        states.insert(0, start_state);
        
        Self {
            states,
            transitions: Vec::new(),
            start_state: 0,
            current_state: 0,
            pattern_mappings: HashMap::new(),
        }
    }

    /// Add a new state to the automaton
    pub fn add_state(&mut self, is_final: bool, pattern_id: Option<String>) -> usize {
        let state_id = self.states.len();
        let state = State {
            id: state_id,
            is_final,
            pattern_id: pattern_id.clone(),
        };
        
        self.states.insert(state_id, state);
        
        if let Some(pid) = pattern_id {
            self.pattern_mappings.insert(state_id, pid);
        }
        
        state_id
    }

    /// Add a transition between states
    pub fn add_transition(&mut self, from: usize, to: usize, condition: TransitionCondition) {
        self.transitions.push(Transition {
            from_state: from,
            to_state: to,
            condition,
        });
    }

    /// Reset the automaton to start state
    pub fn reset(&mut self) {
        self.current_state = self.start_state;
    }

    /// Process an input token and transition states
    pub fn process(&mut self, input: &str) -> Option<String> {
        // Find applicable transitions from current state
        let applicable_transitions: Vec<_> = self.transitions.iter()
            .filter(|t| t.from_state == self.current_state && self.matches_condition(&t.condition, input))
            .collect();
        
        if applicable_transitions.is_empty() {
            return None;
        }
        
        // Take the first matching transition
        let transition = &applicable_transitions[0];
        self.current_state = transition.to_state;
        
        // Check if we reached a final state
        if let Some(state) = self.states.get(&self.current_state) {
            if state.is_final {
                return state.pattern_id.clone();
            }
        }
        
        None
    }

    /// Check if input matches transition condition
    fn matches_condition(&self, condition: &TransitionCondition, input: &str) -> bool {
        match condition {
            TransitionCondition::Action(action) => input.contains(action),
            TransitionCondition::AnyAction => true,
            TransitionCondition::Sequence => input == "seq",
            TransitionCondition::Parallel => input == "parallel",
            TransitionCondition::Token(token) => input.contains(token),
            TransitionCondition::Protocol(protocol) => input.contains(protocol),
            TransitionCondition::Epsilon => true,
        }
    }

    /// Check if automaton is in a final state
    pub fn is_in_final_state(&self) -> bool {
        self.states.get(&self.current_state)
            .map(|s| s.is_final)
            .unwrap_or(false)
    }

    /// Get the pattern ID if in a final state
    pub fn get_matched_pattern(&self) -> Option<String> {
        if self.is_in_final_state() {
            self.pattern_mappings.get(&self.current_state).cloned()
        } else {
            None
        }
    }
}

/// Generator for creating finite automata from patterns
pub struct AutomataGenerator {
    pattern_cache: HashMap<String, FiniteAutomaton>,
}

impl AutomataGenerator {
    pub fn new() -> Self {
        Self {
            pattern_cache: HashMap::new(),
        }
    }

    /// Generate automaton for flash loan pattern
    pub fn generate_flash_loan_automaton(&self, pattern_id: &str) -> FiniteAutomaton {
        let mut automaton = FiniteAutomaton::new();
        
        // State machine for: seq(borrow(...), seq(operations*, repay(...)))
        let s1 = automaton.add_state(false, None); // After seq
        let s2 = automaton.add_state(false, None); // After borrow
        let s3 = automaton.add_state(false, None); // In operations
        let s4 = automaton.add_state(false, None); // After inner seq
        let s5 = automaton.add_state(true, Some(pattern_id.to_string())); // After repay (final)
        
        // Transitions
        automaton.add_transition(0, s1, TransitionCondition::Sequence);
        automaton.add_transition(s1, s2, TransitionCondition::Action("borrow".to_string()));
        automaton.add_transition(s2, s3, TransitionCondition::Sequence);
        automaton.add_transition(s3, s3, TransitionCondition::AnyAction); // Loop for operations
        automaton.add_transition(s3, s4, TransitionCondition::Action("repay".to_string()));
        automaton.add_transition(s4, s5, TransitionCondition::Epsilon);
        
        automaton
    }

    /// Generate automaton for cross-chain pattern
    pub fn generate_cross_chain_automaton(&self, pattern_id: &str) -> FiniteAutomaton {
        let mut automaton = FiniteAutomaton::new();
        
        // State machine for cross-chain operations
        let s1 = automaton.add_state(false, None); // After first chain operations
        let s2 = automaton.add_state(false, None); // After bridge
        let s3 = automaton.add_state(true, Some(pattern_id.to_string())); // After second chain (final)
        
        automaton.add_transition(0, s1, TransitionCondition::Action("onChain".to_string()));
        automaton.add_transition(s1, s2, TransitionCondition::Action("bridge".to_string()));
        automaton.add_transition(s2, s3, TransitionCondition::Action("onChain".to_string()));
        
        automaton
    }

    /// Generate automaton for parallel execution pattern
    pub fn generate_parallel_automaton(&self, pattern_id: &str) -> FiniteAutomaton {
        let mut automaton = FiniteAutomaton::new();
        
        let s1 = automaton.add_state(false, None); // After parallel
        let s2 = automaton.add_state(true, Some(pattern_id.to_string())); // After actions (final)
        
        automaton.add_transition(0, s1, TransitionCondition::Parallel);
        automaton.add_transition(s1, s2, TransitionCondition::AnyAction);
        automaton.add_transition(s2, s2, TransitionCondition::AnyAction); // Multiple parallel actions
        
        automaton
    }

    /// Generate automaton from regex pattern
    pub fn generate_from_regex(&mut self, pattern_id: &str, regex: &str) -> Result<&FiniteAutomaton, AutomataError> {
        // Check cache first
        if self.pattern_cache.contains_key(pattern_id) {
            return Ok(&self.pattern_cache[pattern_id]);
        }
        
        // Validate regex
        let _ = Regex::new(regex).map_err(|_| AutomataError::InvalidPattern {
            pattern: regex.to_string(),
        })?;
        
        // Generate appropriate automaton based on pattern type
        let automaton = if regex.contains("borrow") && regex.contains("repay") {
            self.generate_flash_loan_automaton(pattern_id)
        } else if regex.contains("bridge") {
            self.generate_cross_chain_automaton(pattern_id)
        } else if regex.contains("parallel") {
            self.generate_parallel_automaton(pattern_id)
        } else {
            // Generic automaton for other patterns
            self.generate_generic_automaton(pattern_id)
        };
        
        self.pattern_cache.insert(pattern_id.to_string(), automaton);
        Ok(&self.pattern_cache[pattern_id])
    }

    /// Generate a generic automaton for simple patterns
    fn generate_generic_automaton(&self, pattern_id: &str) -> FiniteAutomaton {
        let mut automaton = FiniteAutomaton::new();
        let final_state = automaton.add_state(true, Some(pattern_id.to_string()));
        automaton.add_transition(0, final_state, TransitionCondition::AnyAction);
        automaton
    }

    /// Merge multiple automata into a single NFA
    pub fn merge_automata(&self, automata: Vec<FiniteAutomaton>) -> FiniteAutomaton {
        let mut merged = FiniteAutomaton::new();
        
        // Add epsilon transitions from start to each automaton's start
        for (idx, automaton) in automata.iter().enumerate() {
            let offset = idx * 100; // Offset to avoid state ID conflicts
            
            // Copy states with offset
            for (state_id, state) in &automaton.states {
                if *state_id != automaton.start_state {
                    let new_id = state_id + offset;
                    merged.states.insert(new_id, State {
                        id: new_id,
                        is_final: state.is_final,
                        pattern_id: state.pattern_id.clone(),
                    });
                    
                    if let Some(pid) = &state.pattern_id {
                        merged.pattern_mappings.insert(new_id, pid.clone());
                    }
                }
            }
            
            // Copy transitions with offset
            for transition in &automaton.transitions {
                let new_from = if transition.from_state == automaton.start_state {
                    0 // Merged start state
                } else {
                    transition.from_state + offset
                };
                
                let new_to = if transition.to_state == automaton.start_state {
                    0
                } else {
                    transition.to_state + offset
                };
                
                merged.add_transition(new_from, new_to, transition.condition.clone());
            }
            
            // Add epsilon transition from merged start
            if offset > 0 {
                merged.add_transition(0, offset, TransitionCondition::Epsilon);
            }
        }
        
        merged
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_flash_loan_automaton() {
        let generator = AutomataGenerator::new();
        let mut automaton = generator.generate_flash_loan_automaton("flash_loan_1");
        
        // Test matching sequence
        automaton.reset();
        assert!(automaton.process("seq").is_none());
        assert!(automaton.process("borrow").is_none());
        assert!(automaton.process("seq").is_none());
        assert!(automaton.process("swap").is_none()); // Some operation
        assert!(automaton.process("repay").is_some());
        assert!(automaton.is_in_final_state());
    }

    #[test]
    fn test_cross_chain_automaton() {
        let generator = AutomataGenerator::new();
        let mut automaton = generator.generate_cross_chain_automaton("cross_chain_1");
        
        automaton.reset();
        assert!(automaton.process("onChain").is_none());
        assert!(automaton.process("bridge").is_none());
        assert!(automaton.process("onChain").is_some());
        assert!(automaton.is_in_final_state());
    }
}