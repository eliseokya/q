//! Bridge types and data structures

use serde::{Deserialize, Serialize};
use common::types::{Chain, Token};
use crate::types::Address;
use std::collections::HashMap;

/// Supported bridge protocols
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Bridge {
    AtomicMesh,
    DeBridge,
    Axelar,
    LayerZero,
}

/// Bridge capability information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BridgeCapability {
    pub bridge: Bridge,
    pub supported_tokens: Vec<Token>,
    pub supported_chains: Vec<Chain>,
    pub min_amount: HashMap<Token, String>,
    pub max_amount: HashMap<Token, String>,
    pub estimated_time_seconds: u64,
    pub base_fee: String,
    pub percentage_fee: f64,
}

/// Bridge endpoint information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BridgeInfo {
    pub bridge: Bridge,
    pub chain: Chain,
    pub contract_address: Address,
    pub version: String,
    pub capabilities: BridgeCapability,
}

/// A specific bridge route between chains
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BridgeRoute {
    pub bridge: Bridge,
    pub from_chain: Chain,
    pub to_chain: Chain,
    pub token: Token,
    pub contract_from: Address,
    pub contract_to: Address,
    pub estimated_time: u64,
    pub total_fee: String,
    pub min_amount: String,
    pub max_amount: String,
}

/// Bridge selection criteria
#[derive(Debug, Clone)]
pub struct BridgeSelectionCriteria {
    pub speed_priority: f64,    // 0.0 = lowest, 1.0 = highest
    pub cost_priority: f64,     // 0.0 = lowest, 1.0 = highest
    pub reliability_priority: f64,
    pub min_liquidity: Option<String>,
}

impl Default for BridgeSelectionCriteria {
    fn default() -> Self {
        Self {
            speed_priority: 0.5,
            cost_priority: 0.5,
            reliability_priority: 0.5,
            min_liquidity: None,
        }
    }
}