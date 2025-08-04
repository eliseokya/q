//! Main bundle generator orchestrator

use std::collections::HashMap;
use std::sync::Arc;
use std::path::Path;
use crate::types::{ExecutionBundle, PatternParameters};
use crate::traits::PatternBundleGenerator;
use crate::registry::{ProtocolRegistry, load_protocol_config};
use crate::patterns::FlashLoanPatternGenerator;
use crate::error::{Result, BundleGeneratorError};
use crate::analysis_result::{AnalysisResult, PatternMatch, PatternType};
use crate::bundle_ext::BundleExt;

/// Main bundle generator that orchestrates pattern-specific generators
pub struct BundleGenerator {
    /// Pattern generators indexed by pattern ID
    generators: HashMap<String, Box<dyn PatternBundleGenerator>>,
    /// Protocol registry shared across generators
    protocol_registry: Arc<ProtocolRegistry>,
}

impl BundleGenerator {
    /// Create a new bundle generator with configuration
    pub fn new(config_path: &Path) -> Result<Self> {
        // Load protocol configuration
        let protocol_registry = Arc::new(load_protocol_config(config_path)?);
        
        // Initialize pattern generators
        let mut generators: HashMap<String, Box<dyn PatternBundleGenerator>> = HashMap::new();
        
        // Register flash loan pattern generator
        let flash_loan_gen = FlashLoanPatternGenerator::new(Arc::clone(&protocol_registry));
        generators.insert(
            flash_loan_gen.pattern_id().to_string(),
            Box::new(flash_loan_gen),
        );
        
        // Additional pattern generators will be added in future phases
        
        Ok(Self {
            generators,
            protocol_registry,
        })
    }
    
    /// Generate an execution bundle from analysis result
    pub fn generate(&self, analysis: AnalysisResult) -> Result<ExecutionBundle> {
        match analysis {
            AnalysisResult::FullMatch {
                pattern,
                bundle,
                confidence,
            } => {
                // Extract pattern parameters from the analysis
                let params = self.extract_pattern_parameters(&pattern, &bundle)?;
                
                // Find the appropriate generator
                let generator = self.generators
                    .get(&params.pattern_id)
                    .ok_or_else(|| BundleGeneratorError::UnknownPattern(params.pattern_id.clone()))?;
                
                // Generate the execution bundle
                let mut exec_bundle = generator.generate(&params)?;
                
                // Add confidence from analysis
                exec_bundle.optimization_hints.gas_optimization_potential = confidence;
                
                Ok(exec_bundle)
            }
            AnalysisResult::PartialMatch { .. } => {
                Err(BundleGeneratorError::ConfigError(
                    "Cannot generate bundle from partial match".to_string()
                ))
            }
            AnalysisResult::Heuristic { .. } => {
                Err(BundleGeneratorError::ConfigError(
                    "Cannot generate bundle from heuristic analysis".to_string()
                ))
            }
            AnalysisResult::Reject { error } => {
                Err(BundleGeneratorError::ConfigError(
                    format!("Analysis rejected: {}", error)
                ))
            }
        }
    }
    
    /// Extract pattern parameters from analysis result
    fn extract_pattern_parameters(
        &self,
        pattern: &PatternMatch,
        bundle: &common::types::Bundle,
    ) -> Result<PatternParameters> {
        // Determine pattern type
        let pattern_id = match &pattern.pattern_type {
            PatternType::FlashLoanArbitrage => "flash-loan-arbitrage",
            PatternType::CrossChainArbitrage => "cross-chain-arbitrage",
            PatternType::TriangularArbitrage => "triangular-arbitrage",
            _ => return Err(BundleGeneratorError::UnknownPattern(
                format!("{:?}", pattern.pattern_type)
            )),
        };
        
        // Extract flash loan parameters if applicable
        let (flash_loan_amount, flash_loan_token, flash_loan_protocol) = 
            if let Some(common::types::Action::Borrow { amount, token, protocol }) = bundle.get_first_action() {
                (
                    Some(format!("{}", amount.num)), // Simple conversion for now
                    Some(token.clone()),
                    Some(protocol.clone()),
                )
            } else {
                (None, None, None)
            };
        
        // Extract all operations
        let operations = bundle.collect_actions();
        
        Ok(PatternParameters {
            pattern_id: pattern_id.to_string(),
            chain: bundle.start_chain.clone(),
            flash_loan_amount,
            flash_loan_token,
            flash_loan_protocol,
            operations,
            constraints: bundle.constraints.clone(),
        })
    }
    
    /// Get list of supported patterns
    pub fn supported_patterns(&self) -> Vec<&str> {
        self.generators.keys().map(|s| s.as_str()).collect()
    }
    
    /// Check if a pattern is supported
    pub fn is_pattern_supported(&self, pattern_id: &str) -> bool {
        self.generators.contains_key(pattern_id)
    }
}