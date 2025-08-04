//! Execution bundle builder utilities

use crate::types::*;
use std::collections::HashMap;
use common::types::Chain;

/// Builder for constructing execution bundles
pub struct ExecutionBundleBuilder {
    bundle_id: Option<String>,
    opportunity_id: Option<String>,
    pattern_id: Option<String>,
    validated: bool,
    atomicity_proof: Option<String>,
    steps: Vec<ExecutionStep>,
    gas_config: Option<GasConfig>,
    profit_config: Option<ProfitConfig>,
    contracts: HashMap<Chain, ChainContracts>,
    optimization_hints: Option<OptimizationHints>,
}

impl ExecutionBundleBuilder {
    /// Create a new builder
    pub fn new() -> Self {
        Self {
            bundle_id: None,
            opportunity_id: None,
            pattern_id: None,
            validated: true,
            atomicity_proof: None,
            steps: Vec::new(),
            gas_config: None,
            profit_config: None,
            contracts: HashMap::new(),
            optimization_hints: None,
        }
    }
    
    /// Set bundle ID
    pub fn bundle_id(mut self, id: String) -> Self {
        self.bundle_id = Some(id);
        self
    }
    
    /// Set opportunity ID
    pub fn opportunity_id(mut self, id: String) -> Self {
        self.opportunity_id = Some(id);
        self
    }
    
    /// Set pattern ID
    pub fn pattern_id(mut self, id: String) -> Self {
        self.pattern_id = Some(id);
        self
    }
    
    /// Set atomicity proof reference
    pub fn atomicity_proof(mut self, proof: String) -> Self {
        self.atomicity_proof = Some(proof);
        self
    }
    
    /// Add an execution step
    pub fn add_step(mut self, step: ExecutionStep) -> Self {
        self.steps.push(step);
        self
    }
    
    /// Set gas configuration
    pub fn gas_config(mut self, config: GasConfig) -> Self {
        self.gas_config = Some(config);
        self
    }
    
    /// Set profit configuration
    pub fn profit_config(mut self, config: ProfitConfig) -> Self {
        self.profit_config = Some(config);
        self
    }
    
    /// Add chain contracts
    pub fn add_chain_contracts(mut self, chain: Chain, contracts: ChainContracts) -> Self {
        self.contracts.insert(chain, contracts);
        self
    }
    
    /// Set optimization hints
    pub fn optimization_hints(mut self, hints: OptimizationHints) -> Self {
        self.optimization_hints = Some(hints);
        self
    }
    
    /// Build the execution bundle
    pub fn build(self) -> Result<ExecutionBundle, String> {
        let bundle_id = self.bundle_id.ok_or("Bundle ID required")?;
        let opportunity_id = self.opportunity_id.ok_or("Opportunity ID required")?;
        let pattern_id = self.pattern_id.ok_or("Pattern ID required")?;
        let atomicity_proof = self.atomicity_proof.ok_or("Atomicity proof required")?;
        let gas_config = self.gas_config.ok_or("Gas config required")?;
        let profit_config = self.profit_config.ok_or("Profit config required")?;
        let optimization_hints = self.optimization_hints.ok_or("Optimization hints required")?;
        
        if self.steps.is_empty() {
            return Err("At least one execution step required".to_string());
        }
        
        Ok(ExecutionBundle {
            bundle_id,
            opportunity_id,
            pattern_id,
            validated: self.validated,
            atomicity_proof,
            execution_plan: ExecutionPlan {
                total_steps: self.steps.len() as u32,
                estimated_duration: 180, // Default 3 minutes
                operations: self.steps,
            },
            gas_config,
            profit_config,
            contracts: self.contracts,
            optimization_hints,
        })
    }
}

impl Default for ExecutionBundleBuilder {
    fn default() -> Self {
        Self::new()
    }
}