//! Configuration loader for protocol registry

use std::path::Path;
use std::fs;
use std::collections::HashMap;
use serde::Deserialize;
use common::types::{Chain, Protocol};
use crate::types::ProtocolInfo;
use crate::registry::ProtocolRegistry;
use crate::error::{Result, BundleGeneratorError};

/// Root configuration structure
#[derive(Debug, Deserialize)]
pub struct ProtocolConfig {
    pub protocols: HashMap<String, ProtocolVersions>,
    pub abis: Option<HashMap<String, serde_json::Value>>,
}

/// Protocol versions across chains
#[derive(Debug, Deserialize)]
pub struct ProtocolVersions {
    pub v3: Option<HashMap<String, ChainProtocolInfo>>,
    pub v2: Option<HashMap<String, ChainProtocolInfo>>,
}

/// Chain-specific protocol information
#[derive(Debug, Clone, Deserialize)]
pub struct ChainProtocolInfo {
    pub pool: String,
    pub oracle: Option<String>,
    pub flash_loan_fee: Option<f64>,
}

/// Load protocol configuration from YAML file
pub fn load_protocol_config(path: &Path) -> Result<ProtocolRegistry> {
    let content = fs::read_to_string(path)
        .map_err(|e| BundleGeneratorError::ConfigError(
            format!("Failed to read config file: {}", e)
        ))?;
    
    let config: ProtocolConfig = serde_yaml::from_str(&content)
        .map_err(|e| BundleGeneratorError::ConfigError(
            format!("Failed to parse YAML: {}", e)
        ))?;
    
    let mut registry = ProtocolRegistry::new();
    
    // Process protocols
    for (protocol_name, versions) in config.protocols {
        let protocol = parse_protocol(&protocol_name)?;
        
        // Process V3
        if let Some(v3_chains) = versions.v3 {
            for (chain_name, info) in v3_chains {
                let chain = parse_chain(&chain_name)?;
                let protocol_info = ProtocolInfo {
                    address: info.pool,
                    abi_name: format!("{}_v3_pool", protocol_name.to_lowercase()),
                    version: "3.0".to_string(),
                    flash_loan_fee: info.flash_loan_fee,
                };
                registry.register_protocol(protocol.clone(), chain, protocol_info);
            }
        }
        
        // Process V2 (if needed in future)
        if let Some(v2_chains) = versions.v2 {
            for (chain_name, info) in v2_chains {
                let chain = parse_chain(&chain_name)?;
                let protocol_info = ProtocolInfo {
                    address: info.pool,
                    abi_name: format!("{}_v2_pool", protocol_name.to_lowercase()),
                    version: "2.0".to_string(),
                    flash_loan_fee: info.flash_loan_fee,
                };
                registry.register_protocol(protocol.clone(), chain, protocol_info);
            }
        }
    }
    
    // Load ABIs if provided
    if let Some(abis) = config.abis {
        for (name, abi) in abis {
            registry.register_abi(name, abi);
        }
    }
    
    Ok(registry)
}

/// Parse protocol name to Protocol enum
fn parse_protocol(name: &str) -> Result<Protocol> {
    match name.to_lowercase().as_str() {
        "aave" => Ok(Protocol::Aave),
        "uniswap" | "uniswapv2" => Ok(Protocol::UniswapV2),
        "compound" => Ok(Protocol::Compound),
        _ => Err(BundleGeneratorError::ConfigError(
            format!("Unknown protocol: {}", name)
        )),
    }
}

/// Parse chain name to Chain enum
fn parse_chain(name: &str) -> Result<Chain> {
    match name.to_lowercase().as_str() {
        "polygon" | "matic" => Ok(Chain::Polygon),
        "arbitrum" | "arb" => Ok(Chain::Arbitrum),
        _ => Err(BundleGeneratorError::ConfigError(
            format!("Unknown or unsupported chain: {} (only Polygon and Arbitrum are supported)", name)
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;
    
    #[test]
    fn test_load_protocol_config() {
        let yaml_content = r#"
protocols:
  aave:
    v3:
      polygon:
        pool: "0x794a61358D6845594F94dc1DB02A252b5b4814aD"
        oracle: "0xb023e699F5a33916Ea823A16485e259257cA8Bd1"
        flash_loan_fee: 0.0009
      arbitrum:
        pool: "0x794a61358D6845594F94dc1DB02A252b5b4814aD"
        flash_loan_fee: 0.0009
"#;
        
        let mut temp_file = NamedTempFile::new().unwrap();
        temp_file.write_all(yaml_content.as_bytes()).unwrap();
        
        let registry = load_protocol_config(temp_file.path()).unwrap();
        
        // Test loaded data
        assert!(registry.is_supported(Protocol::Aave, Chain::Polygon));
        assert!(registry.is_supported(Protocol::Aave, Chain::Arbitrum));
        
        let fee = registry.get_flash_loan_fee(Protocol::Aave, Chain::Polygon).unwrap();
        assert_eq!(fee, Some(0.0009));
    }
}