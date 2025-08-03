//! Parser for extracting theorems from Lean 4 files
//!
//! This module scans .lean files in the maths/ directory and extracts
//! theorem definitions relevant for pattern matching.

use std::fs;
use std::path::{Path, PathBuf};
use regex::Regex;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum LeanParserError {
    #[error("Failed to read file {path}: {source}")]
    FileReadError {
        path: PathBuf,
        source: std::io::Error,
    },
    #[error("Failed to parse theorem: {details}")]
    ParseError { details: String },
}

/// Represents a theorem extracted from Lean files
#[derive(Debug, Clone)]
pub struct ExtractedTheorem {
    pub name: String,
    pub file_path: PathBuf,
    pub line_number: usize,
    pub theorem_type: TheoremType,
    pub pattern_relevant: bool,
    pub content: String,
    pub metadata: TheoremMetadata,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TheoremType {
    FlashLoanPattern,
    CrossChainAtomicity,
    ProtocolInvariant,
    OptimizationRule,
    BridgeSafety,
    GeneralAtomicity,
    Unknown,
}

#[derive(Debug, Clone)]
pub struct TheoremMetadata {
    pub has_atomicity_proof: bool,
    pub involves_cross_chain: bool,
    pub protocol_specific: Option<String>,
    pub optimization_potential: bool,
}

pub struct LeanParser {
    theorem_regex: Regex,
    lemma_regex: Regex,
    def_regex: Regex,
    atomicity_keywords: Vec<String>,
}

impl LeanParser {
    pub fn new() -> Self {
        Self {
            theorem_regex: Regex::new(r"theorem\s+(\w+).*?:=").unwrap(),
            lemma_regex: Regex::new(r"lemma\s+(\w+).*?:=").unwrap(),
            def_regex: Regex::new(r"def\s+(\w+).*?:=").unwrap(),
            atomicity_keywords: vec![
                "IsAtomic".to_string(),
                "atomic".to_string(),
                "flash_loan".to_string(),
                "cross_chain".to_string(),
                "invariant".to_string(),
                "bridge".to_string(),
                "bundle".to_string(),
            ],
        }
    }

    /// Scan a directory recursively for Lean files and extract theorems
    pub fn scan_directory(&self, dir: &Path) -> Result<Vec<ExtractedTheorem>, LeanParserError> {
        let mut theorems = Vec::new();
        self.scan_recursive(dir, &mut theorems)?;
        Ok(theorems)
    }

    fn scan_recursive(&self, dir: &Path, theorems: &mut Vec<ExtractedTheorem>) -> Result<(), LeanParserError> {
        let entries = fs::read_dir(dir).map_err(|e| LeanParserError::FileReadError {
            path: dir.to_path_buf(),
            source: e,
        })?;

        for entry in entries {
            let entry = entry.map_err(|e| LeanParserError::FileReadError {
                path: dir.to_path_buf(),
                source: e,
            })?;
            
            let path = entry.path();
            
            if path.is_dir() {
                self.scan_recursive(&path, theorems)?;
            } else if path.extension().and_then(|s| s.to_str()) == Some("lean") {
                let file_theorems = self.parse_lean_file(&path)?;
                theorems.extend(file_theorems);
            }
        }
        
        Ok(())
    }

    /// Parse a single Lean file and extract theorems
    pub fn parse_lean_file(&self, path: &Path) -> Result<Vec<ExtractedTheorem>, LeanParserError> {
        let content = fs::read_to_string(path).map_err(|e| LeanParserError::FileReadError {
            path: path.to_path_buf(),
            source: e,
        })?;

        let mut theorems = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        for (line_num, line) in lines.iter().enumerate() {
            // Check for theorem declarations
            if let Some(theorem) = self.extract_theorem(line, &lines, line_num, path) {
                if theorem.pattern_relevant {
                    theorems.push(theorem);
                }
            }
        }

        Ok(theorems)
    }

    fn extract_theorem(&self, line: &str, all_lines: &[&str], line_num: usize, file_path: &Path) -> Option<ExtractedTheorem> {
        // Check if this line contains a theorem, lemma, or def
        let name = if let Some(cap) = self.theorem_regex.captures(line) {
            cap.get(1)?.as_str().to_string()
        } else if let Some(cap) = self.lemma_regex.captures(line) {
            cap.get(1)?.as_str().to_string()
        } else if let Some(cap) = self.def_regex.captures(line) {
            cap.get(1)?.as_str().to_string()
        } else {
            return None;
        };

        // Extract the full theorem content (handle multi-line theorems)
        let content = self.extract_full_content(all_lines, line_num);
        
        // Determine theorem type and relevance
        let theorem_type = self.classify_theorem(&name, &content);
        let pattern_relevant = self.is_pattern_relevant(&content, &theorem_type);
        
        // Extract metadata
        let metadata = self.extract_metadata(&content);

        Some(ExtractedTheorem {
            name,
            file_path: file_path.to_path_buf(),
            line_number: line_num + 1, // Convert to 1-indexed
            theorem_type,
            pattern_relevant,
            content,
            metadata,
        })
    }

    fn extract_full_content(&self, lines: &[&str], start_line: usize) -> String {
        let mut content = String::new();
        let mut brace_count = 0;
        let mut in_theorem = false;

        for (i, line) in lines.iter().enumerate().skip(start_line) {
            content.push_str(line);
            content.push('\n');

            // Simple heuristic: count braces to find theorem end
            for ch in line.chars() {
                match ch {
                    '{' | '⟨' => brace_count += 1,
                    '}' | '⟩' => brace_count -= 1,
                    _ => {}
                }
            }

            if line.contains(":=") {
                in_theorem = true;
            }

            // End when we find the next theorem/lemma/def or when braces balance
            if in_theorem && i > start_line {
                if brace_count == 0 && (line.trim().is_empty() || 
                    line.starts_with("theorem") || 
                    line.starts_with("lemma") || 
                    line.starts_with("def") ||
                    line.starts_with("--")) {
                    break;
                }
            }
        }

        content
    }

    fn classify_theorem(&self, name: &str, content: &str) -> TheoremType {
        let lower_name = name.to_lowercase();
        let lower_content = content.to_lowercase();

        if lower_name.contains("flash_loan") || lower_content.contains("flash_loan") {
            TheoremType::FlashLoanPattern
        } else if lower_name.contains("cross_chain") || lower_content.contains("cross_chain") {
            TheoremType::CrossChainAtomicity
        } else if lower_name.contains("invariant") || lower_content.contains("invariant") {
            TheoremType::ProtocolInvariant
        } else if lower_name.contains("optim") || lower_content.contains("optim") {
            TheoremType::OptimizationRule
        } else if lower_name.contains("bridge") || lower_content.contains("bridge") {
            TheoremType::BridgeSafety
        } else if lower_content.contains("isatomic") || lower_content.contains("atomic") {
            TheoremType::GeneralAtomicity
        } else {
            TheoremType::Unknown
        }
    }

    fn is_pattern_relevant(&self, content: &str, theorem_type: &TheoremType) -> bool {
        // All non-unknown theorem types are potentially relevant
        if *theorem_type != TheoremType::Unknown {
            return true;
        }

        // Check for atomicity keywords
        let lower_content = content.to_lowercase();
        self.atomicity_keywords.iter().any(|keyword| {
            lower_content.contains(&keyword.to_lowercase())
        })
    }

    fn extract_metadata(&self, content: &str) -> TheoremMetadata {
        let lower_content = content.to_lowercase();

        TheoremMetadata {
            has_atomicity_proof: lower_content.contains("isatomic") || 
                                lower_content.contains("atomic_execution"),
            involves_cross_chain: lower_content.contains("cross_chain") || 
                                 lower_content.contains("bridge"),
            protocol_specific: self.extract_protocol(&lower_content),
            optimization_potential: lower_content.contains("optim") || 
                                   lower_content.contains("gas_reduction"),
        }
    }

    fn extract_protocol(&self, content: &str) -> Option<String> {
        let protocols = ["uniswap", "aave", "compound", "curve", "balancer"];
        
        for protocol in protocols {
            if content.contains(protocol) {
                return Some(protocol.to_string());
            }
        }
        
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    #[test]
    fn test_parse_simple_theorem() {
        let parser = LeanParser::new();
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.lean");
        
        let content = r#"
theorem flash_loan_atomicity : 
  ∀ (amount : ℚ) (token : Token),
  IsAtomic (borrow amount token ≫ repay amount token) := by
  sorry
"#;
        
        fs::write(&file_path, content).unwrap();
        
        let theorems = parser.parse_lean_file(&file_path).unwrap();
        assert_eq!(theorems.len(), 1);
        assert_eq!(theorems[0].name, "flash_loan_atomicity");
        assert_eq!(theorems[0].theorem_type, TheoremType::FlashLoanPattern);
        assert!(theorems[0].pattern_relevant);
    }
}