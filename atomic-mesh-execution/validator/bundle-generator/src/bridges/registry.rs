//! Bridge registry for managing bridge configurations

use std::collections::HashMap;
use std::path::Path;
use std::fs;
use serde::Deserialize;
use common::types::{Chain, Token};
use crate::bridges::types::{Bridge, BridgeInfo, BridgeCapability, BridgeRoute};
use crate::error::{Result, BundleGeneratorError};

/// Registry for bridge configurations
#[derive(Debug, Clone)]
pub struct BridgeRegistry {
    /// Bridge info indexed by (Bridge, Chain)
    bridges: HashMap<(Bridge, Chain), BridgeInfo>,
    /// Pre-computed routes indexed by (from_chain, to_chain, token)
    routes: HashMap<(Chain, Chain, Token), Vec<BridgeRoute>>,
}

impl BridgeRegistry {
    /// Create a new empty registry
    pub fn new() -> Self {
        Self {
            bridges: HashMap::new(),
            routes: HashMap::new(),
        }
    }
    
    /// Register a bridge endpoint
    pub fn register_bridge(&mut self, info: BridgeInfo) {
        let key = (info.bridge, info.chain.clone());
        self.bridges.insert(key, info);
        self.rebuild_routes();
    }
    
    /// Get bridge info for a specific bridge and chain
    pub fn get_bridge(&self, bridge: Bridge, chain: Chain) -> Option<&BridgeInfo> {
        self.bridges.get(&(bridge, chain))
    }
    
    /// Get all available routes between two chains for a token
    pub fn get_routes(&self, from: Chain, to: Chain, token: Token) -> Vec<&BridgeRoute> {
        self.routes
            .get(&(from, to, token))
            .map(|routes| routes.iter().collect())
            .unwrap_or_default()
    }
    
    /// Find the best route based on criteria
    pub fn find_best_route(
        &self,
        from: Chain,
        to: Chain,
        token: Token,
        _amount: &str,
    ) -> Result<BridgeRoute> {
        let routes = self.get_routes(from.clone(), to.clone(), token.clone());
        
        if routes.is_empty() {
            return Err(BundleGeneratorError::BridgeUnavailable {
                token,
                from,
                to,
            });
        }
        
        // For now, just return the first available route
        // In production, this would score routes based on criteria
        Ok(routes[0].clone())
    }
    
    /// Rebuild the routes cache after bridge updates
    fn rebuild_routes(&mut self) {
        self.routes.clear();
        
        // Generate all possible routes
        for ((bridge, from_chain), from_info) in &self.bridges {
            for ((other_bridge, to_chain), to_info) in &self.bridges {
                if bridge == other_bridge && from_chain != to_chain {
                    // Same bridge can route between chains
                    let common_tokens: Vec<Token> = from_info.capabilities.supported_tokens
                        .iter()
                        .filter(|t| to_info.capabilities.supported_tokens.contains(t))
                        .cloned()
                        .collect();
                    
                    for token in common_tokens {
                        let route = BridgeRoute {
                            bridge: *bridge,
                            from_chain: from_chain.clone(),
                            to_chain: to_chain.clone(),
                            token: token.clone(),
                            contract_from: from_info.contract_address.clone(),
                            contract_to: to_info.contract_address.clone(),
                            estimated_time: from_info.capabilities.estimated_time_seconds,
                            total_fee: from_info.capabilities.base_fee.clone(),
                            min_amount: from_info.capabilities.min_amount
                                .get(&token)
                                .cloned()
                                .unwrap_or_else(|| "0".to_string()),
                            max_amount: from_info.capabilities.max_amount
                                .get(&token)
                                .cloned()
                                .unwrap_or_else(|| "1000000000000000000000".to_string()),
                        };
                        
                        self.routes
                            .entry((from_chain.clone(), to_chain.clone(), token))
                            .or_insert_with(Vec::new)
                            .push(route);
                    }
                }
            }
        }
    }
}

impl Default for BridgeRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Bridge configuration file structure
#[derive(Debug, Deserialize)]
pub struct BridgeConfig {
    pub bridges: HashMap<String, BridgeEndpoints>,
}

#[derive(Debug, Deserialize)]
pub struct BridgeEndpoints {
    pub endpoints: HashMap<String, BridgeEndpointInfo>,
}

#[derive(Debug, Deserialize)]
pub struct BridgeEndpointInfo {
    pub contract: String,
    pub version: String,
    pub supported_tokens: Vec<String>,
    pub min_amounts: HashMap<String, String>,
    pub max_amounts: HashMap<String, String>,
    pub estimated_time: u64,
    pub base_fee: String,
    pub percentage_fee: f64,
}

/// Load bridge configuration from YAML file
pub fn load_bridge_config(path: &Path) -> Result<BridgeRegistry> {
    let content = fs::read_to_string(path)
        .map_err(|e| BundleGeneratorError::ConfigError(
            format!("Failed to read bridge config: {}", e)
        ))?;
    
    let config: BridgeConfig = serde_yaml::from_str(&content)
        .map_err(|e| BundleGeneratorError::ConfigError(
            format!("Failed to parse bridge YAML: {}", e)
        ))?;
    
    let mut registry = BridgeRegistry::new();
    
    for (bridge_name, endpoints) in config.bridges {
        let bridge = parse_bridge(&bridge_name)?;
        
        for (chain_name, endpoint_info) in endpoints.endpoints {
            let chain = parse_chain(&chain_name)?;
            let supported_tokens = endpoint_info.supported_tokens
                .iter()
                .filter_map(|t| parse_token(t).ok())
                .collect();
            
            let mut min_amounts = HashMap::new();
            let mut max_amounts = HashMap::new();
            
            for (token_str, amount) in endpoint_info.min_amounts {
                if let Ok(token) = parse_token(&token_str) {
                    min_amounts.insert(token, amount);
                }
            }
            
            for (token_str, amount) in endpoint_info.max_amounts {
                if let Ok(token) = parse_token(&token_str) {
                    max_amounts.insert(token, amount);
                }
            }
            
            let capabilities = BridgeCapability {
                bridge,
                supported_tokens,
                supported_chains: vec![chain.clone()], // Will be expanded when we have the full registry
                min_amount: min_amounts,
                max_amount: max_amounts,
                estimated_time_seconds: endpoint_info.estimated_time,
                base_fee: endpoint_info.base_fee,
                percentage_fee: endpoint_info.percentage_fee,
            };
            
            let info = BridgeInfo {
                bridge,
                chain: chain.clone(),
                contract_address: endpoint_info.contract,
                version: endpoint_info.version,
                capabilities,
            };
            
            registry.register_bridge(info);
        }
    }
    
    Ok(registry)
}

fn parse_bridge(name: &str) -> Result<Bridge> {
    match name.to_lowercase().as_str() {
        "atomicmesh" | "atomic-mesh" => Ok(Bridge::AtomicMesh),
        "debridge" => Ok(Bridge::DeBridge),
        "axelar" => Ok(Bridge::Axelar),
        "layerzero" | "layer-zero" => Ok(Bridge::LayerZero),
        _ => Err(BundleGeneratorError::ConfigError(
            format!("Unknown bridge: {}", name)
        )),
    }
}

fn parse_chain(name: &str) -> Result<Chain> {
    match name.to_lowercase().as_str() {
        "polygon" | "matic" => Ok(Chain::Polygon),
        "arbitrum" | "arb" => Ok(Chain::Arbitrum),
        _ => Err(BundleGeneratorError::ConfigError(
            format!("Unknown chain: {}", name)
        )),
    }
}

fn parse_token(name: &str) -> Result<Token> {
    match name.to_uppercase().as_str() {
        "WETH" => Ok(Token::WETH),
        "USDC" => Ok(Token::USDC),
        "WBTC" => Ok(Token::WBTC),
        _ => Err(BundleGeneratorError::ConfigError(
            format!("Unknown token: {}", name)
        )),
    }
}