//! Protocol registry for managing protocol configurations across chains

use std::collections::HashMap;
use common::types::{Chain, Protocol};
use crate::types::{ProtocolInfo, Address};
use crate::error::{Result, BundleGeneratorError};

/// Registry for protocol configurations across multiple chains
#[derive(Debug, Clone)]
pub struct ProtocolRegistry {
    /// Protocol configurations indexed by (Protocol, Chain)
    protocols: HashMap<(Protocol, Chain), ProtocolInfo>,
    /// ABI definitions indexed by ABI name
    abis: HashMap<String, serde_json::Value>,
}

impl ProtocolRegistry {
    /// Create a new empty registry
    pub fn new() -> Self {
        Self {
            protocols: HashMap::new(),
            abis: HashMap::new(),
        }
    }
    
    /// Create from a configuration map
    pub fn from_config(
        protocols: HashMap<(Protocol, Chain), ProtocolInfo>,
        abis: HashMap<String, serde_json::Value>,
    ) -> Self {
        Self { protocols, abis }
    }
    
    /// Get protocol contract address for a specific chain
    pub fn get_contract(&self, protocol: Protocol, chain: Chain) -> Result<Address> {
        self.protocols
            .get(&(protocol.clone(), chain.clone()))
            .map(|info| info.address.clone())
            .ok_or_else(|| BundleGeneratorError::ProtocolNotFound {
                protocol: format!("{:?}", protocol),
                chain,
            })
    }
    
    /// Get full protocol info
    pub fn get_protocol_info(&self, protocol: Protocol, chain: Chain) -> Result<&ProtocolInfo> {
        self.protocols
            .get(&(protocol.clone(), chain.clone()))
            .ok_or_else(|| BundleGeneratorError::ProtocolNotFound {
                protocol: format!("{:?}", protocol),
                chain,
            })
    }
    
    /// Get ABI for a protocol
    pub fn get_abi(&self, protocol: Protocol, chain: Chain) -> Result<&serde_json::Value> {
        let info = self.get_protocol_info(protocol, chain)?;
        self.abis
            .get(&info.abi_name)
            .ok_or_else(|| BundleGeneratorError::ConfigError(
                format!("ABI not found: {}", info.abi_name)
            ))
    }
    
    /// Check if a protocol is supported on a chain
    pub fn is_supported(&self, protocol: Protocol, chain: Chain) -> bool {
        self.protocols.contains_key(&(protocol, chain))
    }
    
    /// Get all supported chains for a protocol
    pub fn get_supported_chains(&self, protocol: Protocol) -> Vec<Chain> {
        self.protocols
            .keys()
            .filter(|(p, _)| *p == protocol)
            .map(|(_, c)| c.clone())
            .collect()
    }
    
    /// Get flash loan fee for a protocol (if applicable)
    pub fn get_flash_loan_fee(&self, protocol: Protocol, chain: Chain) -> Result<Option<f64>> {
        self.get_protocol_info(protocol, chain)
            .map(|info| info.flash_loan_fee)
    }
    
    /// Add or update a protocol configuration
    pub fn register_protocol(&mut self, protocol: Protocol, chain: Chain, info: ProtocolInfo) {
        self.protocols.insert((protocol, chain), info);
    }
    
    /// Add or update an ABI
    pub fn register_abi(&mut self, name: String, abi: serde_json::Value) {
        self.abis.insert(name, abi);
    }
}

impl Default for ProtocolRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_protocol_registry() {
        let mut registry = ProtocolRegistry::new();
        
        // Register Aave on Polygon
        let info = ProtocolInfo {
            address: "0x794a61358D6845594F94dc1DB02A252b5b4814aD".to_string(),
            abi_name: "aave_v3_pool".to_string(),
            version: "3.0".to_string(),
            flash_loan_fee: Some(0.0009), // 0.09%
        };
        
        registry.register_protocol(Protocol::Aave, Chain::Polygon, info.clone());
        
        // Test retrieval
        assert_eq!(
            registry.get_contract(Protocol::Aave, Chain::Polygon).unwrap(),
            info.address
        );
        
        // Test unsupported chain (Arbitrum not registered)
        assert!(registry.get_contract(Protocol::Aave, Chain::Arbitrum).is_err());
        
        // Test supported chains
        let chains = registry.get_supported_chains(Protocol::Aave);
        assert_eq!(chains, vec![Chain::Polygon]);
    }
}