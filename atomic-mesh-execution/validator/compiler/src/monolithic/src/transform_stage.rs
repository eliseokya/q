//! Transform actions stage (extracted from transform-actions component)

use serde_json::Value;
use common::{
    CompilerError, PipelineData, TypedAction, Action, Token, Protocol, Chain, Rational,
    transform_errors
};

pub fn process(pipeline_data: &mut PipelineData) -> Result<(), CompilerError> {
    let actions = pipeline_data.actions.take().ok_or_else(|| {
        CompilerError::new(
            "monolithic-transform",
            transform_errors::MISSING_ACTIONS,
            "No actions array in pipeline data".to_string()
        )
    })?;

    // Transform each action
    let mut typed_actions = Vec::with_capacity(actions.len());
    
    for (index, action) in actions.iter().enumerate() {
        // 1. Normalize amounts
        let normalized = normalize_amounts(action, index)?;
        
        // 2. Map to typed action
        let typed_action = map_to_typed(&normalized, index)?;
        
        typed_actions.push(typed_action);
    }

    // 3. Infer chain context
    let source_chain = pipeline_data.metadata.source_chain.as_deref();
    let actions_with_chains = infer_chains(typed_actions, source_chain)?;

    pipeline_data.typed_actions = Some(actions_with_chains);
    Ok(())
}

// Helper function to convert float to Rational (approximation)
fn from_float(f: f64) -> Rational {
    // Simple conversion: multiply by 1000 and use as fraction
    let scaled = (f * 1000.0).round() as u64;
    Rational::new_reduced(scaled, 1000)
}

fn normalize_amounts(action: &Value, _index: usize) -> Result<Value, CompilerError> {
    let mut normalized = action.clone();
    
    if let Some(obj) = normalized.as_object_mut() {
        // Normalize various amount fields to Rational format
        for field in ["amount", "minOut", "min_out"] {
            if let Some(amount_val) = obj.get(field) {
                let rational = parse_to_rational(amount_val)?;
                obj.insert(field.to_string(), serde_json::to_value(rational).unwrap());
            }
        }
    }
    
    Ok(normalized)
}

fn parse_to_rational(value: &Value) -> Result<Rational, CompilerError> {
    match value {
        Value::String(s) => {
            if let Ok(float_val) = s.parse::<f64>() {
                Ok(from_float(float_val))
            } else {
                Err(CompilerError::new(
                    "monolithic-transform",
                    transform_errors::INVALID_AMOUNT,
                    format!("Invalid amount format: {}", s)
                ))
            }
        },
        Value::Number(n) => {
            if let Some(int_val) = n.as_i64() {
                Ok(Rational::from_integer(int_val.abs() as u64))
            } else if let Some(float_val) = n.as_f64() {
                Ok(from_float(float_val))
            } else {
                Err(CompilerError::new(
                    "monolithic-transform",
                    transform_errors::INVALID_AMOUNT,
                    "Invalid number format".to_string()
                ))
            }
        },
        _ => Err(CompilerError::new(
            "monolithic-transform", 
            transform_errors::INVALID_AMOUNT,
            "Amount must be string or number".to_string()
        ))
    }
}

fn map_to_typed(action: &Value, index: usize) -> Result<TypedAction, CompilerError> {
    let obj = action.as_object().ok_or_else(|| {
        CompilerError::new(
            "monolithic-transform",
            transform_errors::INVALID_ACTION,
            format!("Action {} is not an object", index)
        )
    })?;

    let action_type = obj.get("action")
        .and_then(|v| v.as_str())
        .ok_or_else(|| {
            CompilerError::new(
                "monolithic-transform",
                transform_errors::MISSING_ACTION_FIELD,
                format!("Action {} missing 'action' field", index)
            )
        })?;

    let typed_action = match action_type {
        "borrow" => Action::Borrow {
            amount: extract_rational(obj, "amount")?,
            token: extract_token(obj, "token")?,
            protocol: extract_protocol(obj, "protocol")?,
        },
        "repay" => Action::Repay {
            amount: extract_rational(obj, "amount")?,
            token: extract_token(obj, "token")?,
            protocol: extract_protocol(obj, "protocol")?,
        },
        "swap" => Action::Swap {
            amount_in: extract_rational(obj, "amount")?,
            token_in: extract_token(obj, "from")?,
            token_out: extract_token(obj, "to")?,
            min_out: extract_rational(obj, "minOut").or_else(|_| extract_rational(obj, "min_out"))?,
            protocol: extract_protocol(obj, "protocol")?,
        },
        "deposit" => Action::Deposit {
            amount: extract_rational(obj, "amount")?,
            token: extract_token(obj, "token")?,
            protocol: extract_protocol(obj, "protocol")?,
        },
        "withdraw" => Action::Withdraw {
            amount: extract_rational(obj, "amount")?,
            token: extract_token(obj, "token")?,
            protocol: extract_protocol(obj, "protocol")?,
        },
        "bridge" => Action::Bridge {
            chain: extract_chain(obj, "to")?,
            token: extract_token(obj, "token")?,
            amount: extract_rational(obj, "amount")?,
        },
        _ => return Err(CompilerError::new(
            "monolithic-transform",
            "UNKNOWN_ACTION_TYPE",
            format!("Unknown action type: {}", action_type)
        ))
    };

    Ok(TypedAction {
        action: typed_action,
        chain: None, // Will be inferred in next step
    })
}

fn extract_rational(obj: &serde_json::Map<String, Value>, field: &str) -> Result<Rational, CompilerError> {
    let value = obj.get(field).ok_or_else(|| {
        CompilerError::new(
            "monolithic-transform",
            transform_errors::MISSING_ACTION_FIELD,
            format!("Missing required field: {}", field)
        )
    })?;

    if let Some(rational_obj) = value.as_object() {
        // Already in Rational format
        let num = rational_obj.get("num").and_then(|v| v.as_i64()).unwrap_or(0) as u64;
        let den = rational_obj.get("den").and_then(|v| v.as_i64()).unwrap_or(1) as u64;
        Ok(Rational { num, den })
    } else {
        parse_to_rational(value)
    }
}

fn extract_token(obj: &serde_json::Map<String, Value>, field: &str) -> Result<Token, CompilerError> {
    let token_str = obj.get(field)
        .and_then(|v| v.as_str())
        .ok_or_else(|| {
            CompilerError::new(
                "monolithic-transform",
                transform_errors::MISSING_ACTION_FIELD,
                format!("Missing required field: {}", field)
            )
        })?;

    Ok(match token_str.to_uppercase().as_str() {
        "WETH" => Token::WETH,
        "USDC" => Token::USDC,
        "DAI" => Token::DAI,
        "WBTC" => Token::WBTC,
        _ => Token::Custom(token_str.to_string()),
    })
}

fn extract_protocol(obj: &serde_json::Map<String, Value>, field: &str) -> Result<Protocol, CompilerError> {
    let protocol_str = obj.get(field)
        .and_then(|v| v.as_str())
        .ok_or_else(|| {
            CompilerError::new(
                "monolithic-transform",
                transform_errors::MISSING_ACTION_FIELD,
                format!("Missing required field: {}", field)
            )
        })?;

    Ok(match protocol_str.to_lowercase().as_str() {
        "aave" => Protocol::Aave,
        "uniswap" | "uniswapv2" => Protocol::UniswapV2,
        "compound" => Protocol::Compound,
        _ => Protocol::Custom(protocol_str.to_string()),
    })
}

fn extract_chain(obj: &serde_json::Map<String, Value>, field: &str) -> Result<Chain, CompilerError> {
    let chain_str = obj.get(field)
        .and_then(|v| v.as_str())
        .ok_or_else(|| {
            CompilerError::new(
                "monolithic-transform",
                transform_errors::MISSING_ACTION_FIELD,
                format!("Missing required field: {}", field)
            )
        })?;

    Ok(match chain_str.to_lowercase().as_str() {
        "polygon" | "matic" => Chain::Polygon,
        "arbitrum" | "arb" => Chain::Arbitrum,
        _ => return Err(CompilerError::new(
            "monolithic-transform",
            transform_errors::UNKNOWN_CHAIN,
            format!("Unknown chain: {}", chain_str)
        ))
    })
}

fn infer_chains(
    mut actions: Vec<TypedAction>,
    source_chain: Option<&str>,
) -> Result<Vec<TypedAction>, CompilerError> {
    if actions.is_empty() {
        return Ok(actions);
    }

    // Determine starting chain
    let mut current_chain = if let Some(chain_str) = source_chain {
        match chain_str.to_lowercase().as_str() {
            "polygon" | "matic" => Chain::Polygon,
            "arbitrum" | "arb" => Chain::Arbitrum,
            _ => return Err(CompilerError::new(
                "monolithic-transform",
                transform_errors::UNKNOWN_CHAIN,
                format!("Unknown source chain: {}", chain_str)
            ))
        }
    } else {
        Chain::Polygon // Default
    };

    // Track chain context through actions
    for action in actions.iter_mut() {
        match &action.action {
            Action::Bridge { chain: to_chain, .. } => {
                action.chain = Some(current_chain.clone());
                current_chain = to_chain.clone();
            },
            _ => {
                action.chain = Some(current_chain.clone());
            }
        }
    }

    // Validate atomicity (first and last on same chain)
    let first_chain = actions.first().and_then(|a| a.chain.as_ref());
    let last_chain = actions.last().and_then(|a| a.chain.as_ref());

    if let (Some(first), Some(last)) = (first_chain, last_chain) {
        if first != last {
            return Err(CompilerError::new(
                "monolithic-transform",
                transform_errors::CHAIN_MISMATCH,
                "First and last actions must be on the same chain for atomicity".to_string()
            ));
        }
    }

    Ok(actions)
}