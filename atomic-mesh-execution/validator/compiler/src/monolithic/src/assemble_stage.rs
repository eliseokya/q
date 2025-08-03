//! Assemble bundle stage (extracted from assemble-bundle component)

use serde_json::Value;
use common::{CompilerError, PipelineData, Bundle, Constraint, Token, Rational, Chain, Invariant};

// Helper function to convert float to Rational (approximation)
fn from_float(f: f64) -> Rational {
    // Simple conversion: multiply by 1000 and use as fraction
    let scaled = (f * 1000.0).round() as u64;
    Rational::new_reduced(scaled, 1000)
}

pub fn process(pipeline_data: PipelineData) -> Result<Bundle, CompilerError> {
    // Extract expression first
    let expr = pipeline_data.expr.clone().ok_or_else(|| {
        CompilerError::new(
            "monolithic-assemble",
            "MISSING_EXPRESSION",
            "No expression in pipeline data".to_string()
        )
    })?;

    // Extract constraints
    let constraints = extract_constraints(&pipeline_data.constraints)?;

    // Generate bundle name
    let bundle_name = generate_bundle_name(&pipeline_data.metadata.opportunity_id);

    // Determine start chain  
    let start_chain = determine_start_chain(&pipeline_data)?;

    Ok(Bundle {
        name: bundle_name,
        start_chain,
        expr,
        constraints,
    })
}

fn extract_constraints(constraints_json: &Value) -> Result<Vec<Constraint>, CompilerError> {
    let mut constraints = Vec::new();

    if let Some(obj) = constraints_json.as_object() {
        // Extract deadline
        if let Some(deadline_val) = obj.get("deadline") {
            if let Some(blocks) = deadline_val.as_u64() {
                constraints.push(Constraint::Deadline { blocks });
            }
        }

        // Extract max gas
        if let Some(gas_val) = obj.get("max_gas") {
            if let Some(amount) = gas_val.as_u64() {
                constraints.push(Constraint::MaxGas { amount });
            }
        }

        // Extract min balance
        if let Some(balance_obj) = obj.get("min_balance") {
            if let Some(balance) = balance_obj.as_object() {
                if let (Some(token_str), Some(amount_val)) = (
                    balance.get("token").and_then(|v| v.as_str()),
                    balance.get("amount")
                ) {
                    let token = parse_token(token_str);
                    let amount = parse_amount(amount_val)?;
                    constraints.push(Constraint::MinBalance { token, amount });
                }
            }
        }

        // Extract invariants
        if let Some(invariants_arr) = obj.get("invariants").and_then(|v| v.as_array()) {
            for invariant_val in invariants_arr {
                if let Some(invariant_str) = invariant_val.as_str() {
                    let invariant = parse_invariant(invariant_str);
                    constraints.push(Constraint::Invariant { name: invariant });
                }
            }
        }
    }

    Ok(constraints)
}

fn parse_token(token_str: &str) -> Token {
    match token_str.to_uppercase().as_str() {
        "WETH" => Token::WETH,
        "USDC" => Token::USDC,
        "DAI" => Token::DAI,
        "WBTC" => Token::WBTC,
        _ => Token::Custom(token_str.to_string()),
    }
}

fn parse_amount(amount_val: &Value) -> Result<Rational, CompilerError> {
    match amount_val {
        Value::Object(obj) => {
            let num = obj.get("num").and_then(|v| v.as_i64()).unwrap_or(0).abs() as u64;
            let den = obj.get("den").and_then(|v| v.as_i64()).unwrap_or(1).abs() as u64;
            Ok(Rational { num, den })
        },
        Value::String(s) => {
            if let Ok(float_val) = s.parse::<f64>() {
                Ok(from_float(float_val))
            } else {
                Err(CompilerError::new(
                    "monolithic-assemble",
                    "INVALID_AMOUNT",
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
                    "monolithic-assemble",
                    "INVALID_AMOUNT",
                    "Invalid number format".to_string()
                ))
            }
        },
        _ => Err(CompilerError::new(
            "monolithic-assemble",
            "INVALID_AMOUNT",
            "Amount must be object, string, or number".to_string()
        ))
    }
}

fn parse_invariant(invariant_str: &str) -> Invariant {
    match invariant_str.to_lowercase().as_str() {
        "constant_product" => Invariant::ConstantProduct,
        "no_negative_balance" => Invariant::NoNegativeBalance,
        _ => Invariant::ConstantProduct, // Default fallback
    }
}

fn generate_bundle_name(opportunity_id: &str) -> String {
    format!("bundle-{}", opportunity_id)
}

fn determine_start_chain(pipeline_data: &PipelineData) -> Result<Chain, CompilerError> {
    // Try to get from metadata first
    if let Some(ref source_chain) = pipeline_data.metadata.source_chain {
        return Ok(match source_chain.to_lowercase().as_str() {
            "polygon" | "matic" => Chain::Polygon,
            "arbitrum" | "arb" => Chain::Arbitrum,
            _ => Chain::Polygon, // Default
        });
    }

    // Try to get from first typed action
    if let Some(ref typed_actions) = pipeline_data.typed_actions {
        if let Some(first_action) = typed_actions.first() {
            if let Some(ref chain) = first_action.chain {
                return Ok(chain.clone());
            }
        }
    }

    // Default to Polygon
    Ok(Chain::Polygon)
}