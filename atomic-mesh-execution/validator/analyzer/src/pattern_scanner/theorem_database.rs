//! Theorem database for managing extracted mathematical theorems
//!
//! This module stores theorems extracted from Lean files and provides
//! efficient lookup and management capabilities.

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use serde::{Serialize, Deserialize};
use thiserror::Error;

use super::lean_parser::{ExtractedTheorem, TheoremType, TheoremMetadata};

#[derive(Error, Debug)]
pub enum TheoremDatabaseError {
    #[error("Theorem not found: {name}")]
    TheoremNotFound { name: String },
    #[error("Duplicate theorem: {name}")]
    DuplicateTheorem { name: String },
    #[error("Serialization error: {0}")]
    SerializationError(#[from] serde_json::Error),
}

/// A theorem stored in the database with full metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Theorem {
    pub id: String,
    pub name: String,
    pub file_path: PathBuf,
    pub line_number: usize,
    pub theorem_type: TheoremType,
    pub content: String,
    pub metadata: TheoremMetadata,
    pub pattern_hash: String,
    pub dependencies: Vec<String>,
}

/// Database for storing and querying mathematical theorems
#[derive(Debug)]
pub struct TheoremDatabase {
    theorems: HashMap<String, Theorem>,
    theorems_by_type: HashMap<TheoremType, HashSet<String>>,
    theorems_by_file: HashMap<PathBuf, HashSet<String>>,
    pattern_hashes: HashMap<String, String>,
}

impl TheoremDatabase {
    pub fn new() -> Self {
        Self {
            theorems: HashMap::new(),
            theorems_by_type: HashMap::new(),
            theorems_by_file: HashMap::new(),
            pattern_hashes: HashMap::new(),
        }
    }

    /// Add a theorem to the database
    pub fn add_theorem(&mut self, extracted: ExtractedTheorem) -> Result<String, TheoremDatabaseError> {
        let theorem_id = self.generate_id(&extracted.name, &extracted.file_path);
        
        if self.theorems.contains_key(&theorem_id) {
            return Err(TheoremDatabaseError::DuplicateTheorem {
                name: extracted.name.clone(),
            });
        }

        let pattern_hash = self.compute_pattern_hash(&extracted.content);
        let dependencies = self.extract_dependencies(&extracted.content);

        let theorem = Theorem {
            id: theorem_id.clone(),
            name: extracted.name,
            file_path: extracted.file_path.clone(),
            line_number: extracted.line_number,
            theorem_type: extracted.theorem_type.clone(),
            content: extracted.content,
            metadata: extracted.metadata,
            pattern_hash: pattern_hash.clone(),
            dependencies,
        };

        // Update indices
        self.theorems_by_type
            .entry(theorem.theorem_type.clone())
            .or_insert_with(HashSet::new)
            .insert(theorem_id.clone());

        self.theorems_by_file
            .entry(theorem.file_path.clone())
            .or_insert_with(HashSet::new)
            .insert(theorem_id.clone());

        self.pattern_hashes.insert(pattern_hash, theorem_id.clone());
        self.theorems.insert(theorem_id.clone(), theorem);

        Ok(theorem_id)
    }

    /// Get a theorem by ID
    pub fn get_theorem(&self, id: &str) -> Option<&Theorem> {
        self.theorems.get(id)
    }

    /// Get all theorems of a specific type
    pub fn get_theorems_by_type(&self, theorem_type: &TheoremType) -> Vec<&Theorem> {
        self.theorems_by_type
            .get(theorem_type)
            .map(|ids| {
                ids.iter()
                    .filter_map(|id| self.theorems.get(id))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Get all flash loan pattern theorems
    pub fn get_flash_loan_patterns(&self) -> Vec<&Theorem> {
        self.get_theorems_by_type(&TheoremType::FlashLoanPattern)
    }

    /// Get all cross-chain atomicity theorems
    pub fn get_cross_chain_patterns(&self) -> Vec<&Theorem> {
        self.get_theorems_by_type(&TheoremType::CrossChainAtomicity)
    }

    /// Get all theorems from a specific file
    pub fn get_theorems_by_file(&self, file_path: &PathBuf) -> Vec<&Theorem> {
        self.theorems_by_file
            .get(file_path)
            .map(|ids| {
                ids.iter()
                    .filter_map(|id| self.theorems.get(id))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Check if a pattern hash already exists
    pub fn has_pattern_hash(&self, hash: &str) -> bool {
        self.pattern_hashes.contains_key(hash)
    }

    /// Get theorem count by type
    pub fn get_statistics(&self) -> TheoremStatistics {
        let mut stats = TheoremStatistics::default();
        
        for theorem in self.theorems.values() {
            stats.total_count += 1;
            
            match theorem.theorem_type {
                TheoremType::FlashLoanPattern => stats.flash_loan_patterns += 1,
                TheoremType::CrossChainAtomicity => stats.cross_chain_patterns += 1,
                TheoremType::ProtocolInvariant => stats.protocol_invariants += 1,
                TheoremType::OptimizationRule => stats.optimization_rules += 1,
                TheoremType::BridgeSafety => stats.bridge_safety_rules += 1,
                TheoremType::GeneralAtomicity => stats.general_atomicity += 1,
                TheoremType::Unknown => stats.unknown += 1,
            }
        }
        
        stats.unique_files = self.theorems_by_file.len();
        stats
    }

    /// Export database to JSON
    pub fn export_to_json(&self) -> Result<String, TheoremDatabaseError> {
        let theorems: Vec<&Theorem> = self.theorems.values().collect();
        Ok(serde_json::to_string_pretty(&theorems)?)
    }

    /// Import database from JSON
    pub fn import_from_json(&mut self, json: &str) -> Result<usize, TheoremDatabaseError> {
        let theorems: Vec<Theorem> = serde_json::from_str(json)?;
        let count = theorems.len();
        
        for theorem in theorems {
            // Re-add through normal process to rebuild indices
            let extracted = ExtractedTheorem {
                name: theorem.name,
                file_path: theorem.file_path,
                line_number: theorem.line_number,
                theorem_type: theorem.theorem_type,
                pattern_relevant: true,
                content: theorem.content,
                metadata: theorem.metadata,
            };
            
            self.add_theorem(extracted)?;
        }
        
        Ok(count)
    }

    fn generate_id(&self, name: &str, file_path: &PathBuf) -> String {
        let file_stem = file_path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown");
        format!("{}::{}", file_stem, name)
    }

    fn compute_pattern_hash(&self, content: &str) -> String {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        content.hash(&mut hasher);
        format!("{:x}", hasher.finish())
    }

    fn extract_dependencies(&self, content: &str) -> Vec<String> {
        let mut deps = Vec::new();
        
        // Simple heuristic: look for theorem references
        let words: Vec<&str> = content.split_whitespace().collect();
        for (i, word) in words.iter().enumerate() {
            if *word == "apply" || *word == "exact" || *word == "rw" {
                if let Some(next) = words.get(i + 1) {
                    if !next.starts_with('(') && !next.starts_with('[') {
                        deps.push(next.to_string());
                    }
                }
            }
        }
        
        deps
    }
}

#[derive(Debug, Default, Serialize, Deserialize)]
pub struct TheoremStatistics {
    pub total_count: usize,
    pub flash_loan_patterns: usize,
    pub cross_chain_patterns: usize,
    pub protocol_invariants: usize,
    pub optimization_rules: usize,
    pub bridge_safety_rules: usize,
    pub general_atomicity: usize,
    pub unknown: usize,
    pub unique_files: usize,
}

// Make TheoremType serializable
impl Serialize for TheoremType {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            TheoremType::FlashLoanPattern => serializer.serialize_str("FlashLoanPattern"),
            TheoremType::CrossChainAtomicity => serializer.serialize_str("CrossChainAtomicity"),
            TheoremType::ProtocolInvariant => serializer.serialize_str("ProtocolInvariant"),
            TheoremType::OptimizationRule => serializer.serialize_str("OptimizationRule"),
            TheoremType::BridgeSafety => serializer.serialize_str("BridgeSafety"),
            TheoremType::GeneralAtomicity => serializer.serialize_str("GeneralAtomicity"),
            TheoremType::Unknown => serializer.serialize_str("Unknown"),
        }
    }
}

impl<'de> Deserialize<'de> for TheoremType {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        Ok(match s.as_str() {
            "FlashLoanPattern" => TheoremType::FlashLoanPattern,
            "CrossChainAtomicity" => TheoremType::CrossChainAtomicity,
            "ProtocolInvariant" => TheoremType::ProtocolInvariant,
            "OptimizationRule" => TheoremType::OptimizationRule,
            "BridgeSafety" => TheoremType::BridgeSafety,
            "GeneralAtomicity" => TheoremType::GeneralAtomicity,
            _ => TheoremType::Unknown,
        })
    }
}

// Make TheoremMetadata serializable
impl Serialize for TheoremMetadata {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeStruct;
        let mut state = serializer.serialize_struct("TheoremMetadata", 4)?;
        state.serialize_field("has_atomicity_proof", &self.has_atomicity_proof)?;
        state.serialize_field("involves_cross_chain", &self.involves_cross_chain)?;
        state.serialize_field("protocol_specific", &self.protocol_specific)?;
        state.serialize_field("optimization_potential", &self.optimization_potential)?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for TheoremMetadata {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct Helper {
            has_atomicity_proof: bool,
            involves_cross_chain: bool,
            protocol_specific: Option<String>,
            optimization_potential: bool,
        }

        let helper = Helper::deserialize(deserializer)?;
        Ok(TheoremMetadata {
            has_atomicity_proof: helper.has_atomicity_proof,
            involves_cross_chain: helper.involves_cross_chain,
            protocol_specific: helper.protocol_specific,
            optimization_potential: helper.optimization_potential,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_theorem_database() {
        let mut db = TheoremDatabase::new();
        
        let theorem = ExtractedTheorem {
            name: "test_theorem".to_string(),
            file_path: PathBuf::from("test.lean"),
            line_number: 10,
            theorem_type: TheoremType::FlashLoanPattern,
            pattern_relevant: true,
            content: "theorem test_theorem := by sorry".to_string(),
            metadata: TheoremMetadata {
                has_atomicity_proof: true,
                involves_cross_chain: false,
                protocol_specific: None,
                optimization_potential: false,
            },
        };
        
        let id = db.add_theorem(theorem).unwrap();
        assert!(db.get_theorem(&id).is_some());
        
        let stats = db.get_statistics();
        assert_eq!(stats.total_count, 1);
        assert_eq!(stats.flash_loan_patterns, 1);
    }
}