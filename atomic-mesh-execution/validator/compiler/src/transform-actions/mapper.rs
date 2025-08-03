//! Map string values to DSL enum types

use serde_json::{Value, json};
use common::{
    CompilerError, TypedAction, Token, Protocol, Chain, Action, Rational,
    transform_errors
};

/// Map normalized actions to typed actions with enum values
pub fn map_to_typed(action: &Value, index: usize) -> Result<TypedAction, CompilerError> {
    let action_obj = action.as_object()
        .ok_or_else(|| {
            CompilerError::new(
                "transform-actions",
                "INVALID_ACTION",
                format!("Action at index {} is not an object", index)
            )
        })?;

    // Get action type
    let action_type = action_obj.get("action")
        .and_then(|v| v.as_str())
        .ok_or_else(|| {
            CompilerError::new(
                "transform-actions",
                transform_errors::MISSING_ACTION_FIELD,
                format!("Action at index {} missing 'action' field", index)
            )
        })?;

    // Map based on action type
    let typed_action = match action_type.to_lowercase().as_str() {
        "borrow" => {
            let amount = extract_rational(action_obj, "amount", index)?;
            let token = map_token(action_obj, "token", index)?;
            let protocol = map_protocol(action_obj, "protocol", index)?;
            
            Action::Borrow { amount, token, protocol }
        },
        "repay" => {
            let amount = extract_rational(action_obj, "amount", index)?;
            let token = map_token(action_obj, "token", index)?;
            let protocol = map_protocol(action_obj, "protocol", index)?;
            
            Action::Repay { amount, token, protocol }
        },
        "deposit" => {
            let amount = extract_rational(action_obj, "amount", index)?;
            let token = map_token(action_obj, "token", index)?;
            let protocol = map_protocol(action_obj, "protocol", index)?;
            
            Action::Deposit { amount, token, protocol }
        },
        "withdraw" => {
            let amount = extract_rational(action_obj, "amount", index)?;
            let token = map_token(action_obj, "token", index)?;
            let protocol = map_protocol(action_obj, "protocol", index)?;
            
            Action::Withdraw { amount, token, protocol }
        },
        "swap" => {
            // Handle multiple field name variations
            let amount_in = if action_obj.contains_key("amount") {
                extract_rational(action_obj, "amount", index)?
            } else if action_obj.contains_key("amountIn") {
                extract_rational(action_obj, "amountIn", index)?
            } else {
                return Err(CompilerError::new(
                    "transform-actions",
                    transform_errors::MISSING_FIELD,
                    format!("Swap action at index {} missing amount field", index)
                )
                .with_suggestion("Add 'amount' or 'amountIn' field".to_string()));
            };
            
            // Map token fields
            let (token_in, token_out) = if action_obj.contains_key("from") && action_obj.contains_key("to") {
                (
                    map_token(action_obj, "from", index)?,
                    map_token(action_obj, "to", index)?
                )
            } else if action_obj.contains_key("tokenIn") && action_obj.contains_key("tokenOut") {
                (
                    map_token(action_obj, "tokenIn", index)?,
                    map_token(action_obj, "tokenOut", index)?
                )
            } else {
                return Err(CompilerError::new(
                    "transform-actions",
                    transform_errors::MISSING_FIELD,
                    format!("Swap action at index {} missing token fields", index)
                )
                .with_suggestion("Add 'from'/'to' or 'tokenIn'/'tokenOut' fields".to_string()));
            };
            
            // Extract minimum output
            let min_out = if action_obj.contains_key("minOut") {
                extract_rational(action_obj, "minOut", index)?
            } else if action_obj.contains_key("minAmountOut") {
                extract_rational(action_obj, "minAmountOut", index)?
            } else if action_obj.contains_key("expectedOut") {
                extract_rational(action_obj, "expectedOut", index)?
            } else {
                // Default to 0 if not specified (means no minimum)
                Rational::from_integer(0)
            };
            
            let protocol = map_protocol(action_obj, "protocol", index)?;
            
            Action::Swap {
                amount_in,
                token_in,
                token_out,
                min_out,
                protocol
            }
        },
        "bridge" => {
            let to_chain_str = action_obj.get("to")
                .and_then(|v| v.as_str())
                .ok_or_else(|| {
                    CompilerError::new(
                        "transform-actions",
                        transform_errors::MISSING_FIELD,
                        format!("Bridge action at index {} missing 'to' field", index)
                    )
                })?;
            
            let chain = parse_chain(to_chain_str).ok_or_else(|| {
                CompilerError::new(
                    "transform-actions",
                    transform_errors::UNKNOWN_CHAIN,
                    format!("Unknown target chain '{}' in bridge at index {}", to_chain_str, index)
                )
                .with_context(json!({
                    "action_index": index,
                    "provided_chain": to_chain_str
                }))
                .with_suggestion("Supported chains: polygon, arbitrum".to_string())
            })?;
            
            let token = map_token(action_obj, "token", index)?;
            let amount = extract_rational(action_obj, "amount", index)?;
            
            Action::Bridge { chain, token, amount }
        },
        _ => {
            return Err(CompilerError::new(
                "transform-actions",
                transform_errors::INVALID_ACTION,
                format!("Unknown action type '{}' at index {}", action_type, index)
            )
            .with_context(json!({
                "action_index": index,
                "action_type": action_type
            }))
            .with_suggestion("Valid actions: borrow, repay, swap, bridge, deposit, withdraw".to_string()));
        }
    };

    Ok(TypedAction {
        action: typed_action,
        chain: None, // Will be filled by chain_tracker
    })
}

/// Extract rational number from action field
fn extract_rational(
    obj: &serde_json::Map<String, Value>,
    field: &str,
    index: usize
) -> Result<Rational, CompilerError> {
    let value = obj.get(field)
        .ok_or_else(|| {
            CompilerError::new(
                "transform-actions",
                transform_errors::MISSING_FIELD,
                format!("Missing field '{}' at action index {}", field, index)
            )
        })?;
    
    // Should be a rational object {num, den}
    let rational_obj = value.as_object()
        .ok_or_else(|| {
            CompilerError::new(
                "transform-actions",
                "INVALID_RATIONAL",
                format!("Field '{}' should be a rational object with num/den", field)
            )
            .with_context(json!({
                "action_index": index,
                "field": field,
                "value": value
            }))
        })?;
    
    let num = rational_obj.get("num")
        .and_then(|v| v.as_u64())
        .ok_or_else(|| {
            CompilerError::new(
                "transform-actions",
                "INVALID_RATIONAL",
                format!("Invalid or missing 'num' in rational for field '{}'", field)
            )
        })?;
    
    let den = rational_obj.get("den")
        .and_then(|v| v.as_u64())
        .ok_or_else(|| {
            CompilerError::new(
                "transform-actions",
                "INVALID_RATIONAL",
                format!("Invalid or missing 'den' in rational for field '{}'", field)
            )
        })?;
    
    if den == 0 {
        return Err(CompilerError::new(
            "transform-actions",
            "INVALID_RATIONAL",
            format!("Denominator cannot be zero in field '{}'", field)
        ));
    }
    
    Ok(Rational { num, den })
}

/// Map token string to Token enum
fn map_token(
    obj: &serde_json::Map<String, Value>,
    field: &str,
    index: usize
) -> Result<Token, CompilerError> {
    let token_str = obj.get(field)
        .and_then(|v| v.as_str())
        .ok_or_else(|| {
            CompilerError::new(
                "transform-actions",
                transform_errors::MISSING_FIELD,
                format!("Missing or invalid token field '{}' at action index {}", field, index)
            )
        })?;
    
    parse_token(token_str).ok_or_else(|| {
        CompilerError::new(
            "transform-actions",
            transform_errors::UNKNOWN_TOKEN,
            format!("Unknown token '{}' at action index {}", token_str, index)
        )
        .with_context(json!({
            "action_index": index,
            "field": field,
            "provided_token": token_str
        }))
        .with_suggestion(format!(
            "Supported tokens: WETH, USDC, DAI, WBTC. For others, use custom:{}", 
            token_str
        ))
    })
}

/// Map protocol string to Protocol enum
fn map_protocol(
    obj: &serde_json::Map<String, Value>,
    field: &str,
    index: usize
) -> Result<Protocol, CompilerError> {
    let protocol_str = obj.get(field)
        .and_then(|v| v.as_str())
        .ok_or_else(|| {
            CompilerError::new(
                "transform-actions",
                transform_errors::MISSING_FIELD,
                format!("Missing or invalid protocol field '{}' at action index {}", field, index)
            )
        })?;
    
    parse_protocol(protocol_str).ok_or_else(|| {
        CompilerError::new(
            "transform-actions",
            transform_errors::UNKNOWN_PROTOCOL,
            format!("Unknown protocol '{}' at action index {}", protocol_str, index)
        )
        .with_context(json!({
            "action_index": index,
            "field": field,
            "provided_protocol": protocol_str
        }))
        .with_suggestion(format!(
            "Supported protocols: aave, compound, uniswapv2. For others, use custom:{}", 
            protocol_str
        ))
    })
}

/// Parse token string to Token enum
fn parse_token(token_str: &str) -> Option<Token> {
    match token_str.to_uppercase().trim() {
        "WETH" | "ETH" => Some(Token::WETH),
        "USDC" | "USDC.E" => Some(Token::USDC),
        "DAI" => Some(Token::DAI),
        "WBTC" | "BTC" => Some(Token::WBTC),
        _ => {
            // Check if it's a custom token format
            if token_str.starts_with("custom:") {
                let custom_name = token_str.strip_prefix("custom:")?;
                Some(Token::Custom(custom_name.to_string()))
            } else {
                // Auto-convert unknown tokens to custom
                Some(Token::Custom(token_str.to_string()))
            }
        }
    }
}

/// Parse protocol string to Protocol enum
fn parse_protocol(protocol_str: &str) -> Option<Protocol> {
    match protocol_str.to_lowercase().trim() {
        "aave" | "aave-v2" | "aave-v3" => Some(Protocol::Aave),
        "compound" | "compound-v2" | "compound-v3" => Some(Protocol::Compound),
        "uniswap" | "uniswapv2" | "uniswap-v2" => Some(Protocol::UniswapV2),
        _ => {
            // Check if it's a custom protocol format
            if protocol_str.starts_with("custom:") {
                let custom_name = protocol_str.strip_prefix("custom:")?;
                Some(Protocol::Custom(custom_name.to_string()))
            } else {
                // Auto-convert unknown protocols to custom
                Some(Protocol::Custom(protocol_str.to_string()))
            }
        }
    }
}

/// Parse chain string to Chain enum
fn parse_chain(chain_str: &str) -> Option<Chain> {
    match chain_str.to_lowercase().trim() {
        "polygon" | "matic" | "poly" => Some(Chain::Polygon),
        "arbitrum" | "arb" | "arbitrum-one" => Some(Chain::Arbitrum),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn test_map_borrow_action() {
        let action = json!({
            "action": "borrow",
            "amount": {"num": 100, "den": 1},
            "token": "WETH",
            "protocol": "aave"
        });

        let result = map_to_typed(&action, 0).unwrap();
        match result.action {
            Action::Borrow { amount, token, protocol } => {
                assert_eq!(amount.num, 100);
                assert_eq!(amount.den, 1);
                assert_eq!(token, Token::WETH);
                assert_eq!(protocol, Protocol::Aave);
            },
            _ => panic!("Expected Borrow action"),
        }
    }

    #[test]
    fn test_map_swap_action() {
        let action = json!({
            "action": "swap",
            "amount": {"num": 100, "den": 1},
            "from": "WETH",
            "to": "USDC",
            "minOut": {"num": 150000, "den": 1},
            "protocol": "uniswapv2"
        });

        let result = map_to_typed(&action, 0).unwrap();
        match result.action {
            Action::Swap { amount_in, token_in, token_out, min_out, protocol } => {
                assert_eq!(amount_in.num, 100);
                assert_eq!(token_in, Token::WETH);
                assert_eq!(token_out, Token::USDC);
                assert_eq!(min_out.num, 150000);
                assert_eq!(protocol, Protocol::UniswapV2);
            },
            _ => panic!("Expected Swap action"),
        }
    }

    #[test]
    fn test_map_swap_alternate_fields() {
        let action = json!({
            "action": "swap",
            "amountIn": {"num": 100, "den": 1},
            "tokenIn": "DAI",
            "tokenOut": "USDC",
            "minAmountOut": {"num": 99, "den": 1},
            "protocol": "compound"
        });

        let result = map_to_typed(&action, 0).unwrap();
        match result.action {
            Action::Swap { token_in, token_out, .. } => {
                assert_eq!(token_in, Token::DAI);
                assert_eq!(token_out, Token::USDC);
            },
            _ => panic!("Expected Swap action"),
        }
    }

    #[test]
    fn test_map_bridge_action() {
        let action = json!({
            "action": "bridge",
            "to": "arbitrum",
            "token": "WETH",
            "amount": {"num": 100, "den": 1}
        });

        let result = map_to_typed(&action, 0).unwrap();
        match result.action {
            Action::Bridge { chain, token, amount } => {
                assert_eq!(chain, Chain::Arbitrum);
                assert_eq!(token, Token::WETH);
                assert_eq!(amount.num, 100);
            },
            _ => panic!("Expected Bridge action"),
        }
    }

    #[test]
    fn test_token_aliases() {
        assert_eq!(parse_token("weth"), Some(Token::WETH));
        assert_eq!(parse_token("WETH"), Some(Token::WETH));
        assert_eq!(parse_token("ETH"), Some(Token::WETH));
        assert_eq!(parse_token("usdc"), Some(Token::USDC));
        assert_eq!(parse_token("USDC.E"), Some(Token::USDC));
        assert_eq!(parse_token("dai"), Some(Token::DAI));
        assert_eq!(parse_token("wbtc"), Some(Token::WBTC));
        assert_eq!(parse_token("BTC"), Some(Token::WBTC));
    }

    #[test]
    fn test_custom_tokens() {
        assert_eq!(parse_token("LINK"), Some(Token::Custom("LINK".to_string())));
        assert_eq!(parse_token("custom:MKR"), Some(Token::Custom("MKR".to_string())));
        assert_eq!(parse_token("UNI"), Some(Token::Custom("UNI".to_string())));
    }

    #[test]
    fn test_protocol_aliases() {
        assert_eq!(parse_protocol("aave"), Some(Protocol::Aave));
        assert_eq!(parse_protocol("AAVE"), Some(Protocol::Aave));
        assert_eq!(parse_protocol("aave-v2"), Some(Protocol::Aave));
        assert_eq!(parse_protocol("aave-v3"), Some(Protocol::Aave));
        assert_eq!(parse_protocol("compound"), Some(Protocol::Compound));
        assert_eq!(parse_protocol("compound-v2"), Some(Protocol::Compound));
        assert_eq!(parse_protocol("uniswap"), Some(Protocol::UniswapV2));
        assert_eq!(parse_protocol("uniswapv2"), Some(Protocol::UniswapV2));
    }

    #[test]
    fn test_custom_protocols() {
        assert_eq!(parse_protocol("curve"), Some(Protocol::Custom("curve".to_string())));
        assert_eq!(parse_protocol("custom:balancer"), Some(Protocol::Custom("balancer".to_string())));
        assert_eq!(parse_protocol("sushiswap"), Some(Protocol::Custom("sushiswap".to_string())));
    }

    #[test]
    fn test_invalid_rational_den_zero() {
        let action = json!({
            "action": "borrow",
            "amount": {"num": 100, "den": 0},
            "token": "WETH",
            "protocol": "aave"
        });

        let result = map_to_typed(&action, 0);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().code, "INVALID_RATIONAL");
    }

    #[test]
    fn test_missing_required_fields() {
        let action = json!({
            "action": "borrow",
            "amount": {"num": 100, "den": 1}
            // Missing token and protocol
        });

        let result = map_to_typed(&action, 0);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().code, transform_errors::MISSING_FIELD);
    }

    #[test]
    fn test_unknown_action_type() {
        let action = json!({
            "action": "invalid_action",
            "amount": {"num": 100, "den": 1}
        });

        let result = map_to_typed(&action, 0);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().code, transform_errors::INVALID_ACTION);
    }

    #[test]
    fn test_all_action_types() {
        // Test deposit
        let deposit = json!({
            "action": "deposit",
            "amount": {"num": 100, "den": 1},
            "token": "DAI",
            "protocol": "compound"
        });
        assert!(matches!(map_to_typed(&deposit, 0).unwrap().action, Action::Deposit { .. }));

        // Test withdraw
        let withdraw = json!({
            "action": "withdraw",
            "amount": {"num": 50, "den": 1},
            "token": "USDC",
            "protocol": "aave"
        });
        assert!(matches!(map_to_typed(&withdraw, 0).unwrap().action, Action::Withdraw { .. }));

        // Test repay
        let repay = json!({
            "action": "repay",
            "amount": {"num": 100, "den": 1},
            "token": "WETH",
            "protocol": "aave"
        });
        assert!(matches!(map_to_typed(&repay, 0).unwrap().action, Action::Repay { .. }));
    }
}