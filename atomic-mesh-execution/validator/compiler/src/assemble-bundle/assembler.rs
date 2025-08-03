//! Assemble final Bundle structure

use serde_json::Value;
use common::{
    Bundle, Constraint, PipelineData, CompilerError, Chain, Rational,
    assemble_errors
};

/// Assemble the final bundle from pipeline data
pub fn assemble_bundle(pipeline_data: PipelineData) -> Result<Bundle, CompilerError> {
    // Extract expression
    let expr = pipeline_data.expr.ok_or_else(|| {
        CompilerError::new(
            "assemble-bundle",
            assemble_errors::MISSING_EXPRESSION,
            "No expression in pipeline data".to_string()
        )
    })?;

    // Extract metadata
    let metadata = pipeline_data.metadata;

    // Generate bundle name
    let name = generate_bundle_name(&metadata.opportunity_id);

    // Determine start chain
    let start_chain = determine_start_chain(&metadata, &pipeline_data.typed_actions)?;

    // Extract and convert constraints
    let constraints = extract_constraints(pipeline_data.constraints)?;

    Ok(Bundle {
        name,
        start_chain,
        expr,
        constraints,
    })
}

/// Generate a bundle name from opportunity ID
fn generate_bundle_name(opportunity_id: &str) -> String {
    // Clean the opportunity ID for use as a bundle name
    let clean_id = opportunity_id
        .chars()
        .filter(|c| c.is_alphanumeric() || *c == '-' || *c == '_')
        .collect::<String>()
        .to_lowercase();
    
    if clean_id.is_empty() {
        "bundle".to_string()
    } else {
        format!("bundle-{}", clean_id)
    }
}

/// Determine the start chain for the bundle
fn determine_start_chain(
    metadata: &common::Metadata,
    typed_actions: &Option<Vec<common::TypedAction>>,
) -> Result<Chain, CompilerError> {
    // First, check metadata
    if let Some(ref chain_str) = metadata.source_chain {
        return parse_chain(chain_str).ok_or_else(|| {
            CompilerError::new(
                "assemble-bundle",
                assemble_errors::INVALID_CHAIN,
                format!("Invalid source chain in metadata: '{}'", chain_str)
            )
            .with_suggestion("Valid chains: polygon, arbitrum".to_string())
        });
    }

    // Otherwise, check first typed action
    if let Some(ref actions) = typed_actions {
        if let Some(first_action) = actions.first() {
            if let Some(ref chain) = first_action.chain {
                return Ok(chain.clone());
            }
        }
    }

    // Default to polygon
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

/// Extract constraints from JSON value
fn extract_constraints(constraints_value: Value) -> Result<Vec<Constraint>, CompilerError> {
    let constraints_obj = constraints_value.as_object().ok_or_else(|| {
        CompilerError::new(
            "assemble-bundle",
            assemble_errors::INVALID_CONSTRAINTS,
            "Constraints must be an object".to_string()
        )
    })?;

    let mut constraints = Vec::new();

    // Extract deadline constraint
    if let Some(deadline_value) = constraints_obj.get("deadline") {
        if !deadline_value.is_null() {
            let deadline = deadline_value.as_u64().ok_or_else(|| {
                CompilerError::new(
                    "assemble-bundle",
                    assemble_errors::INVALID_CONSTRAINT_VALUE,
                    "Deadline must be a positive integer".to_string()
                )
            })?;
            constraints.push(Constraint::Deadline { blocks: deadline });
        }
    }

    // Extract max gas constraint
    if let Some(max_gas_value) = constraints_obj.get("max_gas") {
        if !max_gas_value.is_null() {
            let max_gas = max_gas_value.as_u64().ok_or_else(|| {
                CompilerError::new(
                    "assemble-bundle",
                    assemble_errors::INVALID_CONSTRAINT_VALUE,
                    "Max gas must be a positive integer".to_string()
                )
            })?;
            constraints.push(Constraint::MaxGas { amount: max_gas });
        }
    }

    // Extract min balance constraint
    if let Some(min_balance_value) = constraints_obj.get("min_balance") {
        if !min_balance_value.is_null() {
            let min_balance_obj = min_balance_value.as_object().ok_or_else(|| {
                CompilerError::new(
                    "assemble-bundle",
                    assemble_errors::INVALID_CONSTRAINT_VALUE,
                    "Min balance must be an object with 'token' and 'amount'".to_string()
                )
            })?;

            let token_str = min_balance_obj.get("token")
                .and_then(|v| v.as_str())
                .ok_or_else(|| {
                    CompilerError::new(
                        "assemble-bundle",
                        assemble_errors::INVALID_CONSTRAINT_VALUE,
                        "Min balance must have 'token' field".to_string()
                    )
                })?;

            let token = parse_token(token_str).ok_or_else(|| {
                CompilerError::new(
                    "assemble-bundle",
                    assemble_errors::INVALID_CONSTRAINT_VALUE,
                    format!("Unknown token in min balance: '{}'", token_str)
                )
            })?;

            let amount = if let Some(amount_obj) = min_balance_obj.get("amount").and_then(|v| v.as_object()) {
                // Rational format
                let num = amount_obj.get("num")
                    .and_then(|v| v.as_u64())
                    .ok_or_else(|| {
                        CompilerError::new(
                            "assemble-bundle",
                            assemble_errors::INVALID_CONSTRAINT_VALUE,
                            "Min balance amount must have 'num' field".to_string()
                        )
                    })?;
                    
                let den = amount_obj.get("den")
                    .and_then(|v| v.as_u64())
                    .ok_or_else(|| {
                        CompilerError::new(
                            "assemble-bundle",
                            assemble_errors::INVALID_CONSTRAINT_VALUE,
                            "Min balance amount must have 'den' field".to_string()
                        )
                    })?;
                    
                Rational { num, den }
            } else if let Some(amount_str) = min_balance_obj.get("amount").and_then(|v| v.as_str()) {
                // String format - parse as decimal
                Rational::from_decimal_str(amount_str).map_err(|e| {
                    CompilerError::new(
                        "assemble-bundle",
                        assemble_errors::INVALID_CONSTRAINT_VALUE,
                        format!("Invalid amount in min balance: {}", e)
                    )
                })?
            } else if let Some(amount_num) = min_balance_obj.get("amount").and_then(|v| v.as_u64()) {
                // Integer format
                Rational::from_integer(amount_num)
            } else {
                return Err(CompilerError::new(
                    "assemble-bundle",
                    assemble_errors::INVALID_CONSTRAINT_VALUE,
                    "Min balance must have 'amount' field".to_string()
                ));
            };

            constraints.push(Constraint::MinBalance { token, amount });
        }
    }

    // Extract invariants
    if let Some(invariants_value) = constraints_obj.get("invariants") {
        if let Some(invariants_array) = invariants_value.as_array() {
            for invariant_value in invariants_array {
                if let Some(invariant_str) = invariant_value.as_str() {
                    match invariant_str {
                        "constant-product" => {
                            constraints.push(Constraint::Invariant { name: common::Invariant::ConstantProduct });
                        },
                        "no-negative-balance" => {
                            constraints.push(Constraint::Invariant { name: common::Invariant::NoNegativeBalance });
                        },
                        _ => {
                            // Unknown invariant - skip with warning
                            // In production, might want to log this
                        }
                    }
                }
            }
        }
    }

    // Extract custom constraints (future extension)
    // For now, we ignore unknown constraint types

    Ok(constraints)
}

/// Parse token string to Token enum
fn parse_token(token_str: &str) -> Option<common::Token> {
    match token_str.to_uppercase().trim() {
        "WETH" | "ETH" => Some(common::Token::WETH),
        "USDC" | "USDC.E" => Some(common::Token::USDC),
        "DAI" => Some(common::Token::DAI),
        "WBTC" | "BTC" => Some(common::Token::WBTC),
        _ => {
            // Custom token
            Some(common::Token::Custom(token_str.to_string()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use common::{Metadata, Expr, Action, Token, Protocol};

    fn create_test_pipeline_data() -> PipelineData {
        PipelineData {
            metadata: Metadata {
                opportunity_id: "test-123".to_string(),
                source_chain: Some("polygon".to_string()),
                target_chain: None,
                timestamp: None,
                expected_profit: None,
                confidence: None,
            },
            actions: None,
            typed_actions: None,
            expr: Some(Expr::Action { action: Action::Borrow {
                amount: Rational::from_integer(100),
                token: Token::WETH,
                protocol: Protocol::Aave,
            } }),
            constraints: json!({
                "deadline": 30,
                "max_gas": 1000000
            }),
        }
    }

    #[test]
    fn test_assemble_basic_bundle() {
        let pipeline_data = create_test_pipeline_data();
        let bundle = assemble_bundle(pipeline_data).unwrap();

        assert_eq!(bundle.name, "bundle-test-123");
        assert_eq!(bundle.start_chain, Chain::Polygon);
        assert!(matches!(bundle.expr, Expr::Action { action: _ }));
        assert_eq!(bundle.constraints.len(), 2);
    }

    #[test]
    fn test_generate_bundle_name() {
        assert_eq!(generate_bundle_name("test-123"), "bundle-test-123");
        assert_eq!(generate_bundle_name("TEST_456"), "bundle-test_456");
        assert_eq!(generate_bundle_name("abc!@#def"), "bundle-abcdef");
        assert_eq!(generate_bundle_name(""), "bundle");
        assert_eq!(generate_bundle_name("!!!"), "bundle");
    }

    #[test]
    fn test_extract_deadline_constraint() {
        let constraints = json!({
            "deadline": 30
        });
        
        let result = extract_constraints(constraints).unwrap();
        assert_eq!(result.len(), 1);
        assert!(matches!(result[0], Constraint::Deadline { blocks: _ }));
    }

    #[test]
    fn test_extract_max_gas_constraint() {
        let constraints = json!({
            "max_gas": 1500000
        });
        
        let result = extract_constraints(constraints).unwrap();
        assert_eq!(result.len(), 1);
        assert!(matches!(result[0], Constraint::MaxGas { amount: _ }));
    }

    #[test]
    fn test_extract_min_balance_constraint() {
        let constraints = json!({
            "min_balance": {
                "token": "USDC",
                "amount": "100.5"
            }
        });
        
        let result = extract_constraints(constraints).unwrap();
        assert_eq!(result.len(), 1);
        match &result[0] {
            Constraint::MinBalance { token, amount } => {
                assert_eq!(*token, Token::USDC);
                assert_eq!(amount.num, 201); // 100.5 = 201/2
                assert_eq!(amount.den, 2);
            },
            _ => panic!("Expected MinBalance constraint"),
        }
    }

    #[test]
    fn test_extract_min_balance_rational_format() {
        let constraints = json!({
            "min_balance": {
                "token": "DAI",
                "amount": {
                    "num": 1000,
                    "den": 3
                }
            }
        });
        
        let result = extract_constraints(constraints).unwrap();
        assert_eq!(result.len(), 1);
        match &result[0] {
            Constraint::MinBalance { token, amount } => {
                assert_eq!(*token, Token::DAI);
                assert_eq!(amount.num, 1000);
                assert_eq!(amount.den, 3);
            },
            _ => panic!("Expected MinBalance constraint"),
        }
    }

    #[test]
    fn test_extract_invariants() {
        let constraints = json!({
            "invariants": ["constant-product", "no-negative-balance"]
        });
        
        let result = extract_constraints(constraints).unwrap();
        assert_eq!(result.len(), 2);
        assert!(matches!(result[0], Constraint::Invariant { name: _ }));
        assert!(matches!(result[1], Constraint::Invariant { name: _ }));
    }

    #[test]
    fn test_null_constraints_ignored() {
        let constraints = json!({
            "deadline": null,
            "max_gas": 1000000,
            "min_balance": null
        });
        
        let result = extract_constraints(constraints).unwrap();
        assert_eq!(result.len(), 1);
        assert!(matches!(result[0], Constraint::MaxGas { amount: _ }));
    }

    #[test]
    fn test_all_constraints() {
        let constraints = json!({
            "deadline": 60,
            "max_gas": 2000000,
            "min_balance": {
                "token": "WETH",
                "amount": "0.1"
            },
            "invariants": ["constant-product"]
        });
        
        let result = extract_constraints(constraints).unwrap();
        assert_eq!(result.len(), 4);
        
        // Check each constraint type is present
        assert!(result.iter().any(|c| matches!(c, Constraint::Deadline { blocks: _ })));
        assert!(result.iter().any(|c| matches!(c, Constraint::MaxGas { amount: _ })));
        assert!(result.iter().any(|c| matches!(c, Constraint::MinBalance { token: _, amount: _ })));
        assert!(result.iter().any(|c| matches!(c, Constraint::Invariant { name: _ })));
    }

    #[test]
    fn test_chain_determination() {
        // From metadata
        let mut data = create_test_pipeline_data();
        assert_eq!(determine_start_chain(&data.metadata, &data.typed_actions).unwrap(), Chain::Polygon);

        // From typed actions when no metadata
        data.metadata.source_chain = None;
        data.typed_actions = Some(vec![
            common::TypedAction {
                action: Action::Borrow {
                    amount: Rational::from_integer(100),
                    token: Token::WETH,
                    protocol: Protocol::Aave,
                },
                chain: Some(Chain::Arbitrum),
            }
        ]);
        assert_eq!(determine_start_chain(&data.metadata, &data.typed_actions).unwrap(), Chain::Arbitrum);

        // Default when nothing available
        data.typed_actions = None;
        assert_eq!(determine_start_chain(&data.metadata, &data.typed_actions).unwrap(), Chain::Polygon);
    }
}