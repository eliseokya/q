//! Bridge router for intelligent bridge selection

use std::sync::Arc;
use common::types::{Chain, Token};
use crate::bridges::types::{Bridge, BridgeRoute, BridgeSelectionCriteria};
use crate::bridges::registry::BridgeRegistry;
use crate::error::{Result, BundleGeneratorError};

/// Bridge router for selecting optimal bridges
pub struct BridgeRouter {
    registry: Arc<BridgeRegistry>,
}

impl BridgeRouter {
    /// Create a new bridge router
    pub fn new(registry: Arc<BridgeRegistry>) -> Self {
        Self { registry }
    }
    
    /// Find the best bridge route based on criteria
    pub fn find_best_route(
        &self,
        from: Chain,
        to: Chain,
        token: Token,
        amount: &str,
        criteria: &BridgeSelectionCriteria,
    ) -> Result<BridgeRoute> {
        let routes = self.registry.get_routes(from.clone(), to.clone(), token.clone());
        
        if routes.is_empty() {
            return Err(BundleGeneratorError::BridgeUnavailable {
                token,
                from,
                to,
            });
        }
        
        // Score each route based on criteria
        let mut scored_routes: Vec<(f64, &BridgeRoute)> = routes
            .into_iter()
            .map(|route| {
                let score = self.score_route(route, criteria, amount);
                (score, route)
            })
            .collect();
        
        // Sort by score (highest first)
        scored_routes.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
        
        // Return the best route
        Ok(scored_routes[0].1.clone())
    }
    
    /// Score a route based on selection criteria
    fn score_route(
        &self,
        route: &BridgeRoute,
        criteria: &BridgeSelectionCriteria,
        amount: &str,
    ) -> f64 {
        let mut score = 0.0;
        
        // Speed score (lower time is better)
        // Normalize to 0-1 where 1 is fastest (< 60s) and 0 is slowest (> 600s)
        let speed_score = (600.0 - route.estimated_time as f64).max(0.0) / 540.0;
        score += speed_score * criteria.speed_priority;
        
        // Cost score (lower fee is better)
        // For now, use a simple heuristic based on base fee
        let fee_value: f64 = route.total_fee.parse().unwrap_or(1000.0);
        let cost_score = (1000.0 - fee_value).max(0.0) / 1000.0;
        score += cost_score * criteria.cost_priority;
        
        // Reliability score (based on bridge type)
        let reliability_score = match route.bridge {
            Bridge::AtomicMesh => 1.0,    // Our own bridge, highest reliability
            Bridge::Axelar => 0.9,         // Well-established
            Bridge::LayerZero => 0.85,     // Good track record
            Bridge::DeBridge => 0.8,       // Newer but solid
        };
        score += reliability_score * criteria.reliability_priority;
        
        // Check liquidity requirements
        if let Some(min_liquidity) = &criteria.min_liquidity {
            let amount_val: f64 = amount.parse().unwrap_or(0.0);
            let min_val: f64 = min_liquidity.parse().unwrap_or(0.0);
            let max_val: f64 = route.max_amount.parse().unwrap_or(0.0);
            
            if amount_val > max_val || amount_val < min_val {
                score *= 0.1; // Heavily penalize if liquidity requirements not met
            }
        }
        
        score
    }
    
    /// Get all available routes with scores
    pub fn get_scored_routes(
        &self,
        from: Chain,
        to: Chain,
        token: Token,
        amount: &str,
        criteria: &BridgeSelectionCriteria,
    ) -> Vec<(f64, BridgeRoute)> {
        self.registry
            .get_routes(from, to, token)
            .into_iter()
            .map(|route| {
                let score = self.score_route(route, criteria, amount);
                (score, route.clone())
            })
            .collect()
    }
    
    /// Check if a bridge route is available
    pub fn is_route_available(
        &self,
        from: Chain,
        to: Chain,
        token: Token,
    ) -> bool {
        !self.registry.get_routes(from, to, token).is_empty()
    }
    
    /// Get estimated bridging time
    pub fn estimate_bridge_time(
        &self,
        from: Chain,
        to: Chain,
        token: Token,
    ) -> Result<u64> {
        let route = self.registry.find_best_route(from, to, token, "0")?;
        Ok(route.estimated_time)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bridges::types::BridgeInfo;
    
    fn create_test_registry() -> Arc<BridgeRegistry> {
        let mut registry = BridgeRegistry::new();
        
        // Add some test bridges
        let bridge_info = BridgeInfo {
            bridge: Bridge::AtomicMesh,
            chain: Chain::Polygon,
            contract_address: "0x1234567890123456789012345678901234567890".to_string(),
            version: "1.0".to_string(),
            capabilities: crate::bridges::types::BridgeCapability {
                bridge: Bridge::AtomicMesh,
                supported_tokens: vec![Token::WETH, Token::USDC],
                supported_chains: vec![Chain::Polygon, Chain::Arbitrum],
                min_amount: std::collections::HashMap::new(),
                max_amount: std::collections::HashMap::new(),
                estimated_time_seconds: 120,
                base_fee: "10".to_string(),
                percentage_fee: 0.001,
            },
        };
        
        registry.register_bridge(bridge_info);
        
        // Add Arbitrum endpoint
        let bridge_info_arb = BridgeInfo {
            bridge: Bridge::AtomicMesh,
            chain: Chain::Arbitrum,
            contract_address: "0x0987654321098765432109876543210987654321".to_string(),
            version: "1.0".to_string(),
            capabilities: crate::bridges::types::BridgeCapability {
                bridge: Bridge::AtomicMesh,
                supported_tokens: vec![Token::WETH, Token::USDC],
                supported_chains: vec![Chain::Polygon, Chain::Arbitrum],
                min_amount: std::collections::HashMap::new(),
                max_amount: std::collections::HashMap::new(),
                estimated_time_seconds: 120,
                base_fee: "10".to_string(),
                percentage_fee: 0.001,
            },
        };
        
        registry.register_bridge(bridge_info_arb);
        
        Arc::new(registry)
    }
    
    #[test]
    fn test_bridge_router_basic() {
        let registry = create_test_registry();
        let router = BridgeRouter::new(registry);
        
        // Test route availability
        assert!(router.is_route_available(Chain::Polygon, Chain::Arbitrum, Token::WETH));
        assert!(router.is_route_available(Chain::Polygon, Chain::Arbitrum, Token::USDC));
        assert!(!router.is_route_available(Chain::Polygon, Chain::Arbitrum, Token::WBTC));
        
        // Test route finding
        let route = router.find_best_route(
            Chain::Polygon,
            Chain::Arbitrum,
            Token::WETH,
            "1000000000000000000",
            &BridgeSelectionCriteria::default(),
        );
        
        assert!(route.is_ok());
        let route = route.unwrap();
        assert_eq!(route.bridge, Bridge::AtomicMesh);
        assert_eq!(route.from_chain, Chain::Polygon);
        assert_eq!(route.to_chain, Chain::Arbitrum);
    }
}