//! Compiler for converting Lean theorems to runtime patterns
//!
//! This module takes theorems from the database and compiles them into
//! efficient runtime patterns for fast matching.

use crate::common::{ProvenPattern, SafetyProperty, PatternTemplate};
use crate::pattern_scanner::{Theorem, TheoremType};
use std::collections::HashMap;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum CompilerError {
    #[error("Unsupported theorem type: {theorem_type:?}")]
    UnsupportedTheoremType { theorem_type: TheoremType },
    #[error("Failed to parse pattern: {details}")]
    ParseError { details: String },
    #[error("Invalid pattern structure: {details}")]
    InvalidPattern { details: String },
}

/// Compiles Lean theorems into runtime patterns
pub struct LeanToPatternCompiler {
    /// Mapping of known theorem patterns to templates
    pattern_templates: HashMap<String, PatternTemplate>,
}

impl LeanToPatternCompiler {
    pub fn new() -> Self {
        let mut pattern_templates = HashMap::new();
        
        // Register known pattern templates
        pattern_templates.insert(
            "flash_loan".to_string(),
            PatternTemplate::FlashLoan,
        );
        pattern_templates.insert(
            "cross_chain_arb".to_string(),
            PatternTemplate::CrossChainArbitrage,
        );
        pattern_templates.insert(
            "triangular_arb".to_string(),
            PatternTemplate::TriangularArbitrage,
        );
        pattern_templates.insert(
            "liquidity_migration".to_string(),
            PatternTemplate::LiquidityMigration,
        );
        
        Self { pattern_templates }
    }

    /// Compile a theorem into a proven pattern
    pub fn compile_theorem(&self, theorem: &Theorem) -> Result<ProvenPattern, CompilerError> {
        match theorem.theorem_type {
            TheoremType::FlashLoanPattern => self.compile_flash_loan_pattern(theorem),
            TheoremType::CrossChainAtomicity => self.compile_cross_chain_pattern(theorem),
            TheoremType::ProtocolInvariant => self.compile_protocol_invariant(theorem),
            TheoremType::OptimizationRule => self.compile_optimization_rule(theorem),
            TheoremType::BridgeSafety => self.compile_bridge_safety_pattern(theorem),
            TheoremType::GeneralAtomicity => self.compile_general_atomicity(theorem),
            TheoremType::Unknown => Err(CompilerError::UnsupportedTheoremType {
                theorem_type: theorem.theorem_type.clone(),
            }),
        }
    }

    fn compile_flash_loan_pattern(&self, theorem: &Theorem) -> Result<ProvenPattern, CompilerError> {
        // Extract pattern structure from theorem content
        let pattern_structure = self.extract_flash_loan_structure(&theorem.content)?;
        
        Ok(ProvenPattern {
            pattern_id: theorem.id.clone(),
            pattern_template: PatternTemplate::FlashLoan,
            theorem_reference: theorem.name.clone(),
            theorem_file: theorem.file_path.clone(),
            theorem_line: theorem.line_number,
            
            // Safety properties derived from the theorem
            safety_properties: vec![
                SafetyProperty::Atomicity,
                SafetyProperty::BalancePreservation,
                SafetyProperty::NoReentrancy,
            ],
            
            // Preconditions extracted from theorem
            preconditions: self.extract_preconditions(&theorem.content),
            
            // Pattern structure for matching
            structure_regex: pattern_structure,
            
            // Confidence based on theorem completeness
            confidence_threshold: 0.95,
            
            // Gas optimization potential
            gas_optimization_potential: theorem.metadata.optimization_potential,
        })
    }

    fn compile_cross_chain_pattern(&self, theorem: &Theorem) -> Result<ProvenPattern, CompilerError> {
        let pattern_structure = self.extract_cross_chain_structure(&theorem.content)?;
        
        Ok(ProvenPattern {
            pattern_id: theorem.id.clone(),
            pattern_template: PatternTemplate::CrossChainArbitrage,
            theorem_reference: theorem.name.clone(),
            theorem_file: theorem.file_path.clone(),
            theorem_line: theorem.line_number,
            safety_properties: vec![
                SafetyProperty::Atomicity,
                SafetyProperty::CrossChainConsistency,
                SafetyProperty::BridgeSafety,
            ],
            preconditions: self.extract_preconditions(&theorem.content),
            structure_regex: pattern_structure,
            confidence_threshold: 0.90,
            gas_optimization_potential: true,
        })
    }

    fn compile_protocol_invariant(&self, theorem: &Theorem) -> Result<ProvenPattern, CompilerError> {
        // Extract which protocol this invariant applies to
        let protocol = theorem.metadata.protocol_specific.as_ref()
            .ok_or_else(|| CompilerError::ParseError {
                details: "Protocol invariant without protocol specification".to_string(),
            })?;
        
        let pattern_structure = format!(r".*protocol:\s*{}\s*.*invariant.*", protocol);
        
        Ok(ProvenPattern {
            pattern_id: theorem.id.clone(),
            pattern_template: PatternTemplate::ProtocolSpecific,
            theorem_reference: theorem.name.clone(),
            theorem_file: theorem.file_path.clone(),
            theorem_line: theorem.line_number,
            safety_properties: vec![
                SafetyProperty::ProtocolInvariant,
                SafetyProperty::StateConsistency,
            ],
            preconditions: self.extract_preconditions(&theorem.content),
            structure_regex: pattern_structure,
            confidence_threshold: 0.98,
            gas_optimization_potential: false,
        })
    }

    fn compile_optimization_rule(&self, theorem: &Theorem) -> Result<ProvenPattern, CompilerError> {
        Ok(ProvenPattern {
            pattern_id: theorem.id.clone(),
            pattern_template: PatternTemplate::GasOptimization,
            theorem_reference: theorem.name.clone(),
            theorem_file: theorem.file_path.clone(),
            theorem_line: theorem.line_number,
            safety_properties: vec![
                SafetyProperty::SemanticEquivalence,
                SafetyProperty::GasReduction,
            ],
            preconditions: self.extract_preconditions(&theorem.content),
            structure_regex: self.extract_optimization_pattern(&theorem.content)?,
            confidence_threshold: 0.85,
            gas_optimization_potential: true,
        })
    }

    fn compile_bridge_safety_pattern(&self, theorem: &Theorem) -> Result<ProvenPattern, CompilerError> {
        Ok(ProvenPattern {
            pattern_id: theorem.id.clone(),
            pattern_template: PatternTemplate::BridgeOperation,
            theorem_reference: theorem.name.clone(),
            theorem_file: theorem.file_path.clone(),
            theorem_line: theorem.line_number,
            safety_properties: vec![
                SafetyProperty::BridgeSafety,
                SafetyProperty::CrossChainConsistency,
                SafetyProperty::TimelockSafety,
            ],
            preconditions: self.extract_preconditions(&theorem.content),
            structure_regex: self.extract_bridge_pattern(&theorem.content)?,
            confidence_threshold: 0.92,
            gas_optimization_potential: false,
        })
    }

    fn compile_general_atomicity(&self, theorem: &Theorem) -> Result<ProvenPattern, CompilerError> {
        Ok(ProvenPattern {
            pattern_id: theorem.id.clone(),
            pattern_template: PatternTemplate::GeneralAtomic,
            theorem_reference: theorem.name.clone(),
            theorem_file: theorem.file_path.clone(),
            theorem_line: theorem.line_number,
            safety_properties: vec![
                SafetyProperty::Atomicity,
                SafetyProperty::AllOrNothing,
            ],
            preconditions: self.extract_preconditions(&theorem.content),
            structure_regex: self.extract_general_pattern(&theorem.content)?,
            confidence_threshold: 0.88,
            gas_optimization_potential: false,
        })
    }

    fn extract_flash_loan_structure(&self, content: &str) -> Result<String, CompilerError> {
        // Pattern: seq(borrow(amount, token, protocol), seq(operations*, repay(amount, token, protocol)))
        if content.contains("borrow") && content.contains("repay") {
            Ok(r"seq\s*\(\s*borrow\s*\([^)]+\)\s*,\s*seq\s*\(.*repay\s*\([^)]+\)\s*\)\s*\)".to_string())
        } else {
            Err(CompilerError::ParseError {
                details: "Flash loan pattern missing borrow/repay structure".to_string(),
            })
        }
    }

    fn extract_cross_chain_structure(&self, _content: &str) -> Result<String, CompilerError> {
        // Pattern: operations on chain A, bridge to chain B, operations on chain B
        Ok(r"seq\s*\(\s*onChain\s*\([^)]+\)\s*,\s*seq\s*\(\s*bridge\s*\([^)]+\)\s*,\s*onChain\s*\([^)]+\)\s*\)\s*\)".to_string())
    }

    fn extract_optimization_pattern(&self, _content: &str) -> Result<String, CompilerError> {
        // Pattern for gas optimization opportunities
        Ok(r"(parallel|batch|optimize)\s*\([^)]+\)".to_string())
    }

    fn extract_bridge_pattern(&self, _content: &str) -> Result<String, CompilerError> {
        // Pattern for bridge operations
        Ok(r"bridge\s*\(\s*(\w+)\s*,\s*(\w+)\s*,\s*([^)]+)\s*\)".to_string())
    }

    fn extract_general_pattern(&self, _content: &str) -> Result<String, CompilerError> {
        // General atomic pattern
        Ok(r"atomic\s*\([^)]+\)".to_string())
    }

    fn extract_preconditions(&self, content: &str) -> Vec<String> {
        let mut preconditions = Vec::new();
        
        // Look for common precondition patterns
        if content.contains("amount > 0") {
            preconditions.push("amount > 0".to_string());
        }
        if content.contains("balance >=") || content.contains("balance ≥") {
            preconditions.push("sufficient_balance".to_string());
        }
        if content.contains("deadline") {
            preconditions.push("within_deadline".to_string());
        }
        if content.contains("liquidity") {
            preconditions.push("sufficient_liquidity".to_string());
        }
        
        preconditions
    }

    /// Batch compile multiple theorems
    pub fn compile_theorems(&self, theorems: &[Theorem]) -> Vec<Result<ProvenPattern, CompilerError>> {
        theorems.iter()
            .map(|theorem| self.compile_theorem(theorem))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;
    use crate::pattern_scanner::lean_parser::TheoremMetadata;

    #[test]
    fn test_compile_flash_loan_theorem() {
        let compiler = LeanToPatternCompiler::new();
        
        let theorem = Theorem {
            id: "test::flash_loan".to_string(),
            name: "flash_loan_atomicity".to_string(),
            file_path: PathBuf::from("test.lean"),
            line_number: 10,
            theorem_type: TheoremType::FlashLoanPattern,
            content: "theorem flash_loan_atomicity : IsAtomic (borrow amount token ≫ ops ≫ repay amount token)".to_string(),
            metadata: TheoremMetadata {
                has_atomicity_proof: true,
                involves_cross_chain: false,
                protocol_specific: Some("aave".to_string()),
                optimization_potential: false,
            },
            pattern_hash: "abc123".to_string(),
            dependencies: vec![],
        };
        
        let pattern = compiler.compile_theorem(&theorem).unwrap();
        assert_eq!(pattern.pattern_template, PatternTemplate::FlashLoan);
        assert!(pattern.safety_properties.contains(&SafetyProperty::Atomicity));
    }
}