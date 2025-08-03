//! Infer chain context from bridge actions

use common::{
    CompilerError, TypedAction, Chain, Action, transform_errors
};
use serde_json::json;

/// Infer chain context for all actions based on bridges and source chain
pub fn infer_chains(
    mut actions: Vec<TypedAction>,
    source_chain: Option<&str>,
) -> Result<Vec<TypedAction>, CompilerError> {
    if actions.is_empty() {
        return Ok(actions);
    }
    
    // Determine starting chain
    let mut current_chain = determine_start_chain(&actions, source_chain)?;
    
    // Track chain context through actions
    for (index, action) in actions.iter_mut().enumerate() {
        match &action.action {
            Action::Bridge { chain: to_chain, .. } => {
                // Bridge changes current chain
                action.chain = Some(current_chain.clone());
                current_chain = to_chain.clone();
            },
            _ => {
                // Non-bridge actions happen on current chain
                action.chain = Some(current_chain.clone());
            }
        }
    }
    
    // Validate chain consistency for atomic execution
    validate_chain_consistency(&actions)?;
    
    Ok(actions)
}

/// Determine the starting chain
fn determine_start_chain(
    actions: &[TypedAction],
    source_chain: Option<&str>,
) -> Result<Chain, CompilerError> {
    // Use provided source chain if available
    if let Some(chain_str) = source_chain {
        return parse_chain(chain_str).ok_or_else(|| {
            CompilerError::new(
                "transform-actions",
                transform_errors::UNKNOWN_CHAIN,
                format!("Unknown source chain: '{}'", chain_str)
            )
            .with_context(json!({
                "provided_chain": chain_str
            }))
            .with_suggestion("Supported chains: polygon, arbitrum".to_string())
        });
    }
    
    // Otherwise, infer from first bridge destination or default
    for (index, action) in actions.iter().enumerate() {
        match &action.action {
            Action::Bridge { chain, .. } => {
                // If the first action is a bridge, we need to infer the source
                // For now, assume we start from polygon if first action is bridge
                if index == 0 {
                    return Ok(Chain::Polygon);
                }
            },
            _ => {
                // First non-bridge action, infer chain from context
                // For now, default to polygon
                return Ok(Chain::Polygon);
            }
        }
    }
    
    // Default to polygon if no indication
    Ok(Chain::Polygon)
}

/// Parse chain string to Chain enum
fn parse_chain(chain_str: &str) -> Option<Chain> {
    match chain_str.to_lowercase().trim() {
        "polygon" | "matic" | "poly" => Some(Chain::Polygon),
        "arbitrum" | "arb" | "arbitrum-one" => Some(Chain::Arbitrum),
        _ => None,
    }
}

/// Validate chain consistency for atomic execution
fn validate_chain_consistency(actions: &[TypedAction]) -> Result<(), CompilerError> {
    if actions.is_empty() {
        return Ok(());
    }
    
    // Check first and last action are on same chain for atomicity
    let first_chain = actions.first().and_then(|a| a.chain.as_ref());
    let last_chain = actions.last().and_then(|a| a.chain.as_ref());
    
    if let (Some(first), Some(last)) = (first_chain, last_chain) {
        if first != last {
            return Err(CompilerError::new(
                "transform-actions",
                transform_errors::CHAIN_MISMATCH,
                "First and last actions must be on the same chain for atomicity".to_string()
            )
            .with_context(json!({
                "first_chain": format!("{:?}", first),
                "last_chain": format!("{:?}", last),
                "first_action": format!("{:?}", actions.first().map(|a| &a.action)),
                "last_action": format!("{:?}", actions.last().map(|a| &a.action))
            }))
            .with_suggestion("Add a bridge action to return to the starting chain".to_string()));
        }
    }
    
    // Validate no orphaned actions (actions after final bridge to nowhere)
    validate_no_orphaned_actions(actions)?;
    
    // Validate protocol availability on chains
    for (index, action) in actions.iter().enumerate() {
        if let Some(chain) = &action.chain {
            validate_protocol_on_chain(&action.action, chain, index)?;
        }
    }
    
    Ok(())
}

/// Check for orphaned actions after bridges
fn validate_no_orphaned_actions(actions: &[TypedAction]) -> Result<(), CompilerError> {
    let mut seen_bridge = false;
    let mut actions_after_bridge = 0;
    
    for action in actions.iter().rev() {
        match &action.action {
            Action::Bridge { .. } => {
                if seen_bridge && actions_after_bridge == 0 {
                    // Multiple bridges at the end with no actions between
                    return Err(CompilerError::new(
                        "transform-actions",
                        transform_errors::INVALID_ACTION_SEQUENCE,
                        "Bridge actions at the end must be followed by actions on the target chain".to_string()
                    )
                    .with_suggestion("Remove unnecessary bridge or add actions on target chain".to_string()));
                }
                seen_bridge = true;
                actions_after_bridge = 0;
            },
            _ => {
                if seen_bridge {
                    actions_after_bridge += 1;
                }
            }
        }
    }
    
    Ok(())
}

/// Validate that a protocol is available on a chain
fn validate_protocol_on_chain(
    action: &Action,
    chain: &Chain,
    index: usize,
) -> Result<(), CompilerError> {
    // For now, all protocols are available on all chains
    // In future, this would check actual protocol deployments
    
    // Example of future validation:
    // match (action, chain) {
    //     (Action::Swap { protocol: Protocol::Custom(name), .. }, Chain::Arbitrum) => {
    //         if name == "polygon-only-dex" {
    //             return Err(...);
    //         }
    //     },
    //     _ => {}
    // }
    
    // Currently no restrictions
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use common::{Token, Protocol, Rational};
    
    #[test]
    fn test_simple_chain_inference() {
        let actions = vec![
            TypedAction {
                action: Action::Borrow {
                    amount: Rational::from_integer(100),
                    token: Token::WETH,
                    protocol: Protocol::Aave,
                },
                chain: None,
            },
            TypedAction {
                action: Action::Bridge {
                    chain: Chain::Arbitrum,
                    token: Token::WETH,
                    amount: Rational::from_integer(100),
                },
                chain: None,
            },
            TypedAction {
                action: Action::Swap {
                    amount_in: Rational::from_integer(100),
                    token_in: Token::WETH,
                    token_out: Token::USDC,
                    min_out: Rational::from_integer(150000),
                    protocol: Protocol::UniswapV2,
                },
                chain: None,
            },
            TypedAction {
                action: Action::Bridge {
                    chain: Chain::Polygon,
                    token: Token::USDC,
                    amount: Rational::from_integer(150000),
                },
                chain: None,
            },
            TypedAction {
                action: Action::Repay {
                    amount: Rational::from_integer(100),
                    token: Token::WETH,
                    protocol: Protocol::Aave,
                },
                chain: None,
            },
        ];
        
        let result = infer_chains(actions, Some("polygon")).unwrap();
        
        assert_eq!(result[0].chain, Some(Chain::Polygon)); // Start
        assert_eq!(result[1].chain, Some(Chain::Polygon)); // Bridge from polygon
        assert_eq!(result[2].chain, Some(Chain::Arbitrum)); // After bridge
        assert_eq!(result[3].chain, Some(Chain::Arbitrum)); // Bridge back from arbitrum
        assert_eq!(result[4].chain, Some(Chain::Polygon)); // End on polygon
    }
    
    #[test]
    fn test_round_trip_chains() {
        let actions = vec![
            TypedAction {
                action: Action::Borrow {
                    amount: Rational::from_integer(100),
                    token: Token::WETH,
                    protocol: Protocol::Aave,
                },
                chain: None,
            },
            TypedAction {
                action: Action::Bridge {
                    chain: Chain::Arbitrum,
                    token: Token::WETH,
                    amount: Rational::from_integer(100),
                },
                chain: None,
            },
            TypedAction {
                action: Action::Swap {
                    amount_in: Rational::from_integer(100),
                    token_in: Token::WETH,
                    token_out: Token::USDC,
                    min_out: Rational::from_integer(150000),
                    protocol: Protocol::UniswapV2,
                },
                chain: None,
            },
            TypedAction {
                action: Action::Bridge {
                    chain: Chain::Polygon,
                    token: Token::USDC,
                    amount: Rational::from_integer(150000),
                },
                chain: None,
            },
            TypedAction {
                action: Action::Repay {
                    amount: Rational::from_integer(100),
                    token: Token::WETH,
                    protocol: Protocol::Aave,
                },
                chain: None,
            },
        ];
        
        let result = infer_chains(actions, Some("polygon")).unwrap();
        
        // Verify round trip
        assert_eq!(result[0].chain, Some(Chain::Polygon)); // Start
        assert_eq!(result[1].chain, Some(Chain::Polygon)); // Bridge from
        assert_eq!(result[2].chain, Some(Chain::Arbitrum)); // On arbitrum
        assert_eq!(result[3].chain, Some(Chain::Arbitrum)); // Bridge from
        assert_eq!(result[4].chain, Some(Chain::Polygon)); // Back on polygon
    }
    
    #[test]
    fn test_chain_mismatch_error() {
        let actions = vec![
            TypedAction {
                action: Action::Borrow {
                    amount: Rational::from_integer(100),
                    token: Token::WETH,
                    protocol: Protocol::Aave,
                },
                chain: None,
            },
            TypedAction {
                action: Action::Bridge {
                    chain: Chain::Arbitrum,
                    token: Token::WETH,
                    amount: Rational::from_integer(100),
                },
                chain: None,
            },
            TypedAction {
                action: Action::Swap {
                    amount_in: Rational::from_integer(100),
                    token_in: Token::WETH,
                    token_out: Token::USDC,
                    min_out: Rational::from_integer(150000),
                    protocol: Protocol::UniswapV2,
                },
                chain: None,
            },
            // Missing bridge back to polygon - ends on Arbitrum instead of Polygon
        ];
        
        let result = infer_chains(actions, Some("polygon"));
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_eq!(err.code, transform_errors::CHAIN_MISMATCH);
    }
    
    #[test]
    fn test_unknown_chain_error() {
        let actions = vec![
            TypedAction {
                action: Action::Borrow {
                    amount: Rational::from_integer(100),
                    token: Token::WETH,
                    protocol: Protocol::Aave,
                },
                chain: None,
            },
        ];
        
        let result = infer_chains(actions, Some("ethereum"));
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_eq!(err.code, transform_errors::UNKNOWN_CHAIN);
    }
    
    #[test]
    fn test_chain_aliases() {
        // Test polygon aliases
        assert_eq!(parse_chain("polygon"), Some(Chain::Polygon));
        assert_eq!(parse_chain("Polygon"), Some(Chain::Polygon));
        assert_eq!(parse_chain("POLYGON"), Some(Chain::Polygon));
        assert_eq!(parse_chain("matic"), Some(Chain::Polygon));
        assert_eq!(parse_chain("poly"), Some(Chain::Polygon));
        
        // Test arbitrum aliases
        assert_eq!(parse_chain("arbitrum"), Some(Chain::Arbitrum));
        assert_eq!(parse_chain("Arbitrum"), Some(Chain::Arbitrum));
        assert_eq!(parse_chain("arb"), Some(Chain::Arbitrum));
        assert_eq!(parse_chain("arbitrum-one"), Some(Chain::Arbitrum));
    }
    
    #[test]
    fn test_default_to_polygon() {
        let actions = vec![
            TypedAction {
                action: Action::Borrow {
                    amount: Rational::from_integer(100),
                    token: Token::WETH,
                    protocol: Protocol::Aave,
                },
                chain: None,
            },
        ];
        
        let result = infer_chains(actions, None).unwrap();
        assert_eq!(result[0].chain, Some(Chain::Polygon));
    }
}