//! Pattern composer for generating new composite patterns
//! 
//! Analyzes sequences of successful pattern matches to identify
//! recurring combinations that can form new composite patterns.

use crate::common::pattern_types::{ProvenPattern, PatternTemplate, SafetyProperty};
use crate::common::analysis_result::AnalysisResult;
use common::Bundle;
use std::collections::HashMap;
use std::path::PathBuf;

/// A composite pattern discovered from successful matches
#[derive(Debug, Clone)]
pub struct CompositePattern {
    /// Unique identifier for the composite pattern
    pub id: String,
    /// Component patterns that make up this composite
    pub components: Vec<String>,
    /// Combined safety properties
    pub safety_properties: Vec<SafetyProperty>,
    /// Frequency of occurrence
    pub frequency: usize,
    /// Average confidence when matched
    pub avg_confidence: f64,
    /// Description of the pattern
    pub description: String,
}

/// Pattern sequence that might form a composite
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
struct PatternSequence {
    patterns: Vec<String>,
}

/// Pattern composer that discovers new composite patterns
pub struct PatternComposer {
    /// History of successful pattern matches
    match_history: Vec<(String, AnalysisResult, Bundle)>,
    /// Discovered pattern sequences
    sequence_frequency: HashMap<PatternSequence, usize>,
    /// Minimum frequency for composite pattern
    min_frequency: usize,
    /// Minimum confidence for composite pattern
    min_confidence: f64,
}

impl PatternComposer {
    /// Create a new pattern composer
    pub fn new() -> Self {
        Self {
            match_history: Vec::new(),
            sequence_frequency: HashMap::new(),
            min_frequency: 3,
            min_confidence: 0.8,
        }
    }

    /// Record a successful pattern match
    pub fn record_match(&mut self, pattern_id: String, result: AnalysisResult, bundle: Bundle) {
        self.match_history.push((pattern_id, result, bundle));
        
        // Analyze sequences after each new match
        self.analyze_sequences();
    }

    /// Analyze match history for recurring sequences
    fn analyze_sequences(&mut self) {
        // Look for sequences of 2-4 patterns
        for window_size in 2..=4 {
            if self.match_history.len() < window_size {
                continue;
            }
            
            // Sliding window over match history
            for window in self.match_history.windows(window_size) {
                let patterns: Vec<String> = window.iter()
                    .map(|(id, _, _)| id.clone())
                    .collect();
                
                let sequence = PatternSequence { patterns };
                *self.sequence_frequency.entry(sequence).or_insert(0) += 1;
            }
        }
    }

    /// Discover composite patterns from frequent sequences
    pub fn discover_composites(&self) -> Vec<CompositePattern> {
        let mut composites = Vec::new();
        
        for (sequence, frequency) in &self.sequence_frequency {
            if *frequency >= self.min_frequency {
                // Calculate average confidence for this sequence
                let avg_confidence = self.calculate_sequence_confidence(sequence);
                
                if avg_confidence >= self.min_confidence {
                    let composite = self.create_composite_pattern(sequence, *frequency, avg_confidence);
                    composites.push(composite);
                }
            }
        }
        
        composites
    }

    /// Calculate average confidence for a pattern sequence
    fn calculate_sequence_confidence(&self, sequence: &PatternSequence) -> f64 {
        let mut total_confidence = 0.0;
        let mut count = 0;
        
        // Find all occurrences of this sequence in history
        for window in self.match_history.windows(sequence.patterns.len()) {
            let window_patterns: Vec<String> = window.iter()
                .map(|(id, _, _)| id.clone())
                .collect();
            
            if window_patterns == sequence.patterns {
                // Extract confidence from results
                for (_, result, _) in window {
                    let confidence = match result {
                        AnalysisResult::FullMatch { confidence, .. } => *confidence,
                        AnalysisResult::PartialMatch { confidence, .. } => *confidence,
                        AnalysisResult::Heuristic { confidence, .. } => *confidence,
                        _ => 0.0,
                    };
                    total_confidence += confidence;
                    count += 1;
                }
            }
        }
        
        if count > 0 {
            total_confidence / count as f64
        } else {
            0.0
        }
    }

    /// Create a composite pattern from a sequence
    fn create_composite_pattern(
        &self,
        sequence: &PatternSequence,
        frequency: usize,
        avg_confidence: f64
    ) -> CompositePattern {
        // Generate ID from component patterns
        let id = format!("composite_{}", sequence.patterns.join("_"));
        
        // Collect safety properties from all components
        let mut safety_properties = Vec::new();
        for _pattern_id in &sequence.patterns {
            // In a real implementation, we'd look up the pattern's properties
            // For now, we'll use common properties
            safety_properties.push(SafetyProperty::Atomicity);
        }
        
        // Generate description
        let description = format!(
            "Composite pattern of {} components: {}",
            sequence.patterns.len(),
            sequence.patterns.join(" → ")
        );
        
        CompositePattern {
            id,
            components: sequence.patterns.clone(),
            safety_properties,
            frequency,
            avg_confidence,
            description,
        }
    }

    /// Convert a composite pattern to a ProvenPattern
    pub fn composite_to_proven(&self, composite: &CompositePattern) -> ProvenPattern {
        ProvenPattern {
            pattern_id: composite.id.clone(),
            pattern_template: PatternTemplate::GeneralAtomic, // Composites are general
            theorem_reference: format!("composite:{}", composite.id),
            theorem_file: PathBuf::from("discovery/composites.lean"),
            theorem_line: 0,
            safety_properties: composite.safety_properties.clone(),
            preconditions: vec![
                format!("Requires {} component patterns", composite.components.len())
            ],
            structure_regex: self.generate_composite_regex(&composite.components),
            confidence_threshold: composite.avg_confidence * 0.9, // Slightly lower threshold
            gas_optimization_potential: true, // Composites often optimize gas
        }
    }

    /// Generate a regex pattern for the composite
    fn generate_composite_regex(&self, components: &[String]) -> String {
        // Simple regex that matches the sequence
        components.join(".*")
    }

    /// Get match history statistics
    pub fn get_statistics(&self) -> ComposerStatistics {
        ComposerStatistics {
            total_matches: self.match_history.len(),
            unique_patterns: self.match_history.iter()
                .map(|(id, _, _)| id)
                .collect::<std::collections::HashSet<_>>()
                .len(),
            discovered_composites: self.discover_composites().len(),
            frequent_sequences: self.sequence_frequency.iter()
                .filter(|(_, freq)| **freq >= self.min_frequency)
                .count(),
        }
    }

    /// Clear match history
    pub fn clear_history(&mut self) {
        self.match_history.clear();
        self.sequence_frequency.clear();
    }
}

/// Statistics about pattern composition
#[derive(Debug, Clone)]
pub struct ComposerStatistics {
    pub total_matches: usize,
    pub unique_patterns: usize,
    pub discovered_composites: usize,
    pub frequent_sequences: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use common::types::{Expr, Action, Chain, Token, Protocol, Rational};
    use crate::common::analysis_result::ValidationRecommendation;

    #[test]
    fn test_pattern_composer_creation() {
        let composer = PatternComposer::new();
        assert_eq!(composer.match_history.len(), 0);
    }

    #[test]
    fn test_composite_discovery() {
        let mut composer = PatternComposer::new();
        composer.min_frequency = 2; // Lower threshold for testing
        
        // Create test bundle
        let bundle = Bundle {
            name: "test".to_string(),
            start_chain: Chain::Polygon,
            expr: Expr::Action {
                action: Action::Swap {
                    amount_in: Rational::from_integer(100),
                    token_in: Token::WETH,
                    token_out: Token::USDC,
                    min_out: Rational::from_integer(95),
                    protocol: Protocol::UniswapV2,
                }
            },
            constraints: vec![],
        };
        
        // Record a pattern sequence multiple times
        for _ in 0..3 {
            composer.record_match(
                "pattern_a".to_string(),
                AnalysisResult::FullMatch {
                    theorem_reference: "test".to_string(),
                    confidence: 0.9,
                    safety_guarantees: vec![],
                    gas_optimization_available: false,
                    execution_plan: "test".to_string(),
                },
                bundle.clone()
            );
            
            composer.record_match(
                "pattern_b".to_string(),
                AnalysisResult::FullMatch {
                    theorem_reference: "test".to_string(),
                    confidence: 0.85,
                    safety_guarantees: vec![],
                    gas_optimization_available: false,
                    execution_plan: "test".to_string(),
                },
                bundle.clone()
            );
        }
        
        // Discover composites
        let composites = composer.discover_composites();
        assert!(!composites.is_empty());
        
        // Find the composite with 2 components (pattern_a -> pattern_b)
        let two_component_composite = composites.iter()
            .find(|c| c.components.len() == 2)
            .expect("Should find a 2-component composite");
        
        // Check both patterns are present
        assert!(two_component_composite.components.contains(&"pattern_a".to_string()));
        assert!(two_component_composite.components.contains(&"pattern_b".to_string()));
        assert!(two_component_composite.frequency >= 2);
        assert!(two_component_composite.avg_confidence > 0.8);
    }
}