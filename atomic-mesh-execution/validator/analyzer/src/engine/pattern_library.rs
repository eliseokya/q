//! Static pattern library for managing pre-compiled mathematical patterns
//!
//! This module manages the collection of proven patterns compiled from the
//! mathematical theorems in the maths/ directory.

use crate::common::{ProvenPattern, SafetyProperty, PatternTemplate};
use crate::pattern_scanner::{LeanParser, TheoremDatabase};
use crate::pattern_compiler::LeanToPatternCompiler;
use std::collections::HashMap;
use std::path::Path;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum PatternLibraryError {
    #[error("Pattern not found: {pattern_id}")]
    PatternNotFound { pattern_id: String },
    #[error("Duplicate pattern ID: {pattern_id}")]
    DuplicatePattern { pattern_id: String },
    #[error("Invalid pattern structure: {details}")]
    InvalidPattern { details: String },
    #[error("Pattern compilation failed: {details}")]
    CompilationFailed { details: String },
}

/// Static pattern library containing pre-compiled proven patterns
pub struct StaticPatternLibrary {
    patterns: HashMap<String, ProvenPattern>,
    patterns_by_template: HashMap<PatternTemplate, Vec<String>>,
    pattern_metadata: HashMap<String, PatternMetadata>,
}

#[derive(Debug, Clone)]
pub struct PatternMetadata {
    pub theorem_file: String,
    pub theorem_line: usize,
    pub compilation_timestamp: String,
    pub pattern_complexity: PatternComplexity,
    pub verification_level: VerificationLevel,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PatternComplexity {
    Simple,      // Single action patterns
    Composite,   // Sequential patterns  
    Complex,     // Parallel + cross-chain patterns
    Advanced,    // Complex mathematical structures
}

#[derive(Debug, Clone)]
pub enum VerificationLevel {
    Proven,      // Fully proven in Lean 4
    Heuristic,   // Structurally sound but unproven
    Experimental, // Under development
}

impl StaticPatternLibrary {
    /// Create a new empty pattern library
    pub fn new() -> Self {
        Self {
            patterns: HashMap::new(),
            patterns_by_template: HashMap::new(),
            pattern_metadata: HashMap::new(),
        }
    }

    /// Load patterns from the maths/ directory
    pub fn load() -> Result<Self, PatternLibraryError> {
        let mut library = Self::new();
        
        // Path to maths directory (relative to workspace root)
        let maths_path = Path::new("../../../maths");
        
        if !maths_path.exists() {
            log::warn!("Maths directory not found at {:?}, using empty pattern library", maths_path);
            return Ok(library);
        }
        
        log::info!("Scanning maths directory for theorems...");
        
        // Scan for theorems
        let parser = LeanParser::new();
        let theorems = parser.scan_directory(maths_path)
            .map_err(|e| PatternLibraryError::CompilationFailed {
                details: format!("Failed to scan maths directory: {}", e),
            })?;
        
        log::info!("Found {} theorems in maths directory", theorems.len());
        
        // Build theorem database
        let mut database = TheoremDatabase::new();
        for theorem in theorems {
            database.add_theorem(theorem)
                .map_err(|e| PatternLibraryError::CompilationFailed {
                    details: format!("Failed to add theorem to database: {}", e),
                })?;
        }
        
        let stats = database.get_statistics();
        log::info!("Theorem statistics: {} flash loan patterns, {} cross-chain patterns, {} protocol invariants",
            stats.flash_loan_patterns, stats.cross_chain_patterns, stats.protocol_invariants);
        
        // Compile theorems to patterns
        let compiler = LeanToPatternCompiler::new();
        let all_theorems: Vec<_> = database.get_flash_loan_patterns().into_iter()
            .chain(database.get_cross_chain_patterns())
            .collect();
        
        for theorem in all_theorems {
            match compiler.compile_theorem(theorem) {
                Ok(pattern) => {
                    library.add_pattern(pattern)?;
                }
                Err(e) => {
                    log::warn!("Failed to compile theorem {}: {}", theorem.name, e);
                }
            }
        }
        
        log::info!("Successfully loaded {} patterns", library.patterns.len());
        
        Ok(library)
    }

    /// Create a pattern library with default proven patterns
    pub fn with_default_patterns() -> Result<Self, PatternLibraryError> {
        let mut library = Self::new();
        library.load_default_patterns()?;
        Ok(library)
    }

    /// Load default patterns from mathematical theorems
    fn load_default_patterns(&mut self) -> Result<(), PatternLibraryError> {
        // Flash loan patterns from maths/Stack/Bundles.lean
        self.add_pattern(create_flash_loan_pattern())?;
        
        // Cross-chain arbitrage patterns
        self.add_pattern(create_cross_chain_arbitrage_pattern())?;
        
        // Parallel execution patterns  
        self.add_pattern(create_parallel_execution_pattern())?;
        
        // Sequential operation patterns
        self.add_pattern(create_sequential_pattern())?;
        
        // Bridge operation patterns
        self.add_pattern(create_bridge_pattern())?;

        log::info!("Loaded {} default patterns", self.patterns.len());
        Ok(())
    }

    /// Add a pattern to the library
    pub fn add_pattern(&mut self, pattern: ProvenPattern) -> Result<(), PatternLibraryError> {
        // Check for duplicates
        if self.patterns.contains_key(&pattern.id) {
            return Err(PatternLibraryError::DuplicatePattern { 
                pattern_id: pattern.id.clone() 
            });
        }

        // Validate pattern structure
        self.validate_pattern(&pattern)?;

        // Create metadata
        let metadata = PatternMetadata {
            theorem_file: self.extract_theorem_file(&pattern.lean_theorem),
            theorem_line: self.extract_theorem_line(&pattern.lean_theorem),
            compilation_timestamp: chrono::Utc::now().to_rfc3339(),
            pattern_complexity: self.assess_pattern_complexity(&pattern),
            verification_level: VerificationLevel::Proven,
        };

        // Index by template type
        let template = self.infer_pattern_template(&pattern);
        self.patterns_by_template
            .entry(template)
            .or_insert_with(Vec::new)
            .push(pattern.id.clone());

        // Store pattern and metadata
        self.pattern_metadata.insert(pattern.id.clone(), metadata);
        self.patterns.insert(pattern.id.clone(), pattern);

        Ok(())
    }

    /// Get a pattern by ID
    pub fn get_pattern(&self, pattern_id: &str) -> Option<&ProvenPattern> {
        self.patterns.get(pattern_id)
    }

    /// Get all patterns of a specific template type
    pub fn get_patterns_by_template(&self, template: &PatternTemplate) -> Vec<&ProvenPattern> {
        self.patterns_by_template
            .get(template)
            .map(|ids| ids.iter().filter_map(|id| self.patterns.get(id)).collect())
            .unwrap_or_default()
    }

    /// Get all proven patterns (for analyzer engine)
    pub fn get_all_patterns(&self) -> Vec<ProvenPattern> {
        self.patterns.values().cloned().collect()
    }

    /// Get pattern metadata
    pub fn get_metadata(&self, pattern_id: &str) -> Option<&PatternMetadata> {
        self.pattern_metadata.get(pattern_id)
    }

    /// Get library statistics
    pub fn get_statistics(&self) -> LibraryStatistics {
        let total_patterns = self.patterns.len();
        let by_template: HashMap<PatternTemplate, usize> = self.patterns_by_template
            .iter()
            .map(|(template, ids)| (*template, ids.len()))
            .collect();
        
        let by_complexity: HashMap<PatternComplexity, usize> = self.pattern_metadata
            .values()
            .fold(HashMap::new(), |mut acc, metadata| {
                *acc.entry(metadata.pattern_complexity.clone()).or_insert(0) += 1;
                acc
            });

        LibraryStatistics {
            total_patterns,
            patterns_by_template: by_template,
            patterns_by_complexity: by_complexity,
        }
    }

    /// Remove a pattern from the library
    pub fn remove_pattern(&mut self, pattern_id: &str) -> Result<ProvenPattern, PatternLibraryError> {
        let pattern = self.patterns.remove(pattern_id)
            .ok_or_else(|| PatternLibraryError::PatternNotFound { 
                pattern_id: pattern_id.to_string() 
            })?;

        // Remove from template index
        let template = self.infer_pattern_template(&pattern);
        if let Some(ids) = self.patterns_by_template.get_mut(&template) {
            ids.retain(|id| id != pattern_id);
        }

        // Remove metadata
        self.pattern_metadata.remove(pattern_id);

        Ok(pattern)
    }

    /// Validate pattern structure and properties
    fn validate_pattern(&self, pattern: &ProvenPattern) -> Result<(), PatternLibraryError> {
        // Check ID is not empty
        if pattern.id.is_empty() {
            return Err(PatternLibraryError::InvalidPattern {
                details: "Pattern ID cannot be empty".to_string(),
            });
        }

        // Check theorem reference exists
        if pattern.lean_theorem.is_empty() {
            return Err(PatternLibraryError::InvalidPattern {
                details: "Lean theorem reference cannot be empty".to_string(),
            });
        }

        // Check confidence is valid
        if !(0.0..=1.0).contains(&pattern.confidence) {
            return Err(PatternLibraryError::InvalidPattern {
                details: "Pattern confidence must be between 0.0 and 1.0".to_string(),
            });
        }

        Ok(())
    }

    /// Helper functions for pattern analysis
    fn extract_theorem_file(&self, theorem_ref: &str) -> String {
        theorem_ref.split(':').next().unwrap_or("unknown").to_string()
    }

    fn extract_theorem_line(&self, theorem_ref: &str) -> usize {
        theorem_ref.split(':').nth(1)
            .and_then(|s| s.parse().ok())
            .unwrap_or(0)
    }

    fn assess_pattern_complexity(&self, pattern: &ProvenPattern) -> PatternComplexity {
        match pattern.safety_properties.len() {
            1..=2 => PatternComplexity::Simple,
            3..=4 => PatternComplexity::Composite,
            5..=6 => PatternComplexity::Complex,
            _ => PatternComplexity::Advanced,
        }
    }

    fn infer_pattern_template(&self, pattern: &ProvenPattern) -> PatternTemplate {
        // Simple heuristic based on pattern name
        if pattern.name.contains("flash") || pattern.name.contains("loan") {
            PatternTemplate::FlashLoan
        } else if pattern.name.contains("cross") || pattern.name.contains("chain") {
            PatternTemplate::CrossChainArbitrage
        } else if pattern.name.contains("parallel") {
            PatternTemplate::Parallel
        } else if pattern.name.contains("seq") {
            PatternTemplate::Sequential
        } else {
            PatternTemplate::Action
        }
    }
}

#[derive(Debug, Clone)]
pub struct LibraryStatistics {
    pub total_patterns: usize,
    pub patterns_by_template: HashMap<PatternTemplate, usize>,
    pub patterns_by_complexity: HashMap<PatternComplexity, usize>,
}

impl Default for StaticPatternLibrary {
    fn default() -> Self {
        Self::new()
    }
}

/// Factory functions for creating default patterns
fn create_flash_loan_pattern() -> ProvenPattern {
    ProvenPattern {
        id: "flash_loan_atomic".to_string(),
        name: "Flash Loan Atomicity Pattern".to_string(),
        lean_theorem: "maths/Stack/Bundles.lean:FlashLoanAtomic".to_string(),
        safety_properties: vec![
            SafetyProperty::Atomic,
            SafetyProperty::BalancePreserving,
            SafetyProperty::GasBounded,
        ],
        confidence: 1.0, // Fully proven
    }
}

fn create_cross_chain_arbitrage_pattern() -> ProvenPattern {
    ProvenPattern {
        id: "cross_chain_arbitrage".to_string(),
        name: "Cross-Chain Arbitrage Pattern".to_string(),
        lean_theorem: "maths/examples/BridgedFlashLoan.lean:CrossChainAtomic".to_string(),
        safety_properties: vec![
            SafetyProperty::Atomic,
            SafetyProperty::CrossChainSafe,
            SafetyProperty::BalancePreserving,
        ],
        confidence: 1.0,
    }
}

fn create_parallel_execution_pattern() -> ProvenPattern {
    ProvenPattern {
        id: "parallel_execution".to_string(),
        name: "Parallel Execution Pattern".to_string(),
        lean_theorem: "maths/Optimization/Parallel.lean:ParallelSafe".to_string(),
        safety_properties: vec![
            SafetyProperty::Atomic,
            SafetyProperty::GasBounded,
        ],
        confidence: 0.95, // High confidence
    }
}

fn create_sequential_pattern() -> ProvenPattern {
    ProvenPattern {
        id: "sequential_operations".to_string(),
        name: "Sequential Operations Pattern".to_string(),
        lean_theorem: "maths/DSL/Compile.lean:SequentialComposition".to_string(),
        safety_properties: vec![
            SafetyProperty::InvariantPreserving,
            SafetyProperty::BalancePreserving,
        ],
        confidence: 1.0,
    }
}

fn create_bridge_pattern() -> ProvenPattern {
    ProvenPattern {
        id: "bridge_operation".to_string(),
        name: "Bridge Operation Pattern".to_string(),
        lean_theorem: "maths/Bridge/Naturality.lean:BridgeNaturality".to_string(),
        safety_properties: vec![
            SafetyProperty::CrossChainSafe,
            SafetyProperty::DeadlineRespecting,
        ],
        confidence: 0.98,
    }
}