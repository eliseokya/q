//! Normalize string amounts to rational numbers

use serde_json::{Value, json};
use common::{CompilerError, Rational, transform_errors};

/// Normalize all amount fields in an action to rational numbers
pub fn normalize_amounts(action: &Value, index: usize) -> Result<Value, CompilerError> {
    let mut action_obj = action.as_object()
        .ok_or_else(|| {
            CompilerError::new(
                "transform-actions",
                "INVALID_ACTION",
                format!("Action at index {} is not an object", index)
            )
        })?
        .clone();

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

    // Normalize based on action type
    match action_type.to_lowercase().as_str() {
        "borrow" | "repay" | "deposit" | "withdraw" => {
            normalize_field(&mut action_obj, "amount", index)?;
        },
        "swap" => {
            // Handle multiple possible field names for swap amount
            if action_obj.contains_key("amount") {
                normalize_field(&mut action_obj, "amount", index)?;
            } else if action_obj.contains_key("amountIn") {
                normalize_field(&mut action_obj, "amountIn", index)?;
            }
            
            // Handle output amount fields
            if action_obj.contains_key("minOut") {
                normalize_field(&mut action_obj, "minOut", index)?;
            } else if action_obj.contains_key("minAmountOut") {
                normalize_field(&mut action_obj, "minAmountOut", index)?;
            } else if action_obj.contains_key("expectedOut") {
                normalize_field(&mut action_obj, "expectedOut", index)?;
            }
        },
        "bridge" => {
            normalize_field(&mut action_obj, "amount", index)?;
        },
        _ => {
            // Unknown action type, will be caught in mapper
        }
    }

    Ok(Value::Object(action_obj))
}

/// Normalize a single amount field to rational
fn normalize_field(
    obj: &mut serde_json::Map<String, Value>,
    field: &str,
    action_index: usize,
) -> Result<(), CompilerError> {
    if let Some(value) = obj.get(field) {
        let rational = parse_amount_value(value).map_err(|e| {
            CompilerError::new(
                "transform-actions",
                transform_errors::INVALID_AMOUNT,
                format!("Invalid amount in field '{}': {}", field, e)
            )
            .with_context(json!({
                "action_index": action_index,
                "field": field,
                "value": value.to_string(),
                "value_type": value_type_name(value)
            }))
            .with_suggestion(suggest_amount_fix(value))
        })?;

        // Check for negative or zero amounts
        if rational.num == 0 && rational.den != 0 {
            return Err(CompilerError::new(
                "transform-actions",
                transform_errors::NEGATIVE_AMOUNT,
                format!("Amount cannot be zero in field '{}'", field)
            )
            .with_context(json!({
                "action_index": action_index,
                "field": field
            }))
            .with_suggestion("Amounts must be positive numbers".to_string()));
        }

        obj.insert(field.to_string(), json!({
            "num": rational.num,
            "den": rational.den
        }));
    }

    Ok(())
}

/// Parse an amount value (string or number) to rational
fn parse_amount_value(value: &Value) -> Result<Rational, String> {
    match value {
        Value::String(s) => {
            // Clean the string first
            let cleaned = s.trim();
            
            // Check for empty string
            if cleaned.is_empty() {
                return Err("Empty amount string".to_string());
            }
            
            // Check for negative values
            if cleaned.starts_with('-') {
                return Err("Negative amounts not allowed".to_string());
            }
            
            // Parse using rational's decimal parser
            Rational::from_decimal_str(cleaned)
        },
        Value::Number(n) => {
            if let Some(i) = n.as_u64() {
                Ok(Rational::from_integer(i))
            } else if let Some(f) = n.as_f64() {
                if f < 0.0 {
                    Err("Negative amounts not allowed".to_string())
                } else if f.is_nan() || f.is_infinite() {
                    Err("Invalid numeric value (NaN or Infinity)".to_string())
                } else {
                    // Convert float to string and parse to avoid precision issues
                    Rational::from_decimal_str(&f.to_string())
                }
            } else {
                Err("Invalid number format".to_string())
            }
        },
        _ => Err(format!("Expected string or number, got {}", value_type_name(value))),
    }
}

/// Get helpful suggestion for amount fixes
fn suggest_amount_fix(value: &Value) -> String {
    match value {
        Value::String(s) => {
            if s.contains(',') {
                "Remove commas from numbers (use '1000' not '1,000')".to_string()
            } else if s.contains('$') || s.contains('€') || s.contains('£') {
                "Remove currency symbols from amounts".to_string()
            } else if s.trim().is_empty() {
                "Provide a valid numeric amount".to_string()
            } else {
                "Use numeric format: '123.45' or 123.45".to_string()
            }
        },
        Value::Array(_) => "Amount should be a single value, not an array".to_string(),
        Value::Object(_) => "Amount should be a number or string, not an object".to_string(),
        Value::Bool(_) => "Amount cannot be a boolean value".to_string(),
        Value::Null => "Amount cannot be null".to_string(),
        _ => "Provide amount as a string or number".to_string(),
    }
}

/// Get human-readable type name for error messages
fn value_type_name(value: &Value) -> &'static str {
    match value {
        Value::Null => "null",
        Value::Bool(_) => "boolean",
        Value::Number(_) => "number",
        Value::String(_) => "string",
        Value::Array(_) => "array",
        Value::Object(_) => "object",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn test_normalize_borrow() {
        let action = json!({
            "action": "borrow",
            "amount": "100",
            "token": "WETH",
            "protocol": "aave"
        });

        let result = normalize_amounts(&action, 0).unwrap();
        let obj = result.as_object().unwrap();
        assert_eq!(obj["amount"]["num"], 100);
        assert_eq!(obj["amount"]["den"], 1);
    }

    #[test]
    fn test_normalize_decimal() {
        let action = json!({
            "action": "borrow",
            "amount": "100.5"
        });

        let result = normalize_amounts(&action, 0).unwrap();
        let obj = result.as_object().unwrap();
        assert_eq!(obj["amount"]["num"], 201);
        assert_eq!(obj["amount"]["den"], 2);
    }

    #[test]
    fn test_normalize_swap_multiple_fields() {
        let action = json!({
            "action": "swap",
            "amount": "1.5",
            "minOut": "150000"
        });

        let result = normalize_amounts(&action, 0).unwrap();
        let obj = result.as_object().unwrap();
        assert_eq!(obj["amount"]["num"], 3);
        assert_eq!(obj["amount"]["den"], 2);
        assert_eq!(obj["minOut"]["num"], 150000);
        assert_eq!(obj["minOut"]["den"], 1);
    }

    #[test]
    fn test_normalize_swap_alternate_fields() {
        let action = json!({
            "action": "swap",
            "amountIn": "100",
            "minAmountOut": "150"
        });

        let result = normalize_amounts(&action, 0).unwrap();
        let obj = result.as_object().unwrap();
        assert_eq!(obj["amountIn"]["num"], 100);
        assert_eq!(obj["minAmountOut"]["num"], 150);
    }

    #[test]
    fn test_normalize_scientific() {
        let action = json!({
            "action": "borrow",
            "amount": "1e18"
        });

        let result = normalize_amounts(&action, 0).unwrap();
        let obj = result.as_object().unwrap();
        assert_eq!(obj["amount"]["num"], 1_000_000_000_000_000_000u64);
        assert_eq!(obj["amount"]["den"], 1);
    }

    #[test]
    fn test_normalize_number_type() {
        let action = json!({
            "action": "borrow",
            "amount": 123
        });

        let result = normalize_amounts(&action, 0).unwrap();
        let obj = result.as_object().unwrap();
        assert_eq!(obj["amount"]["num"], 123);
        assert_eq!(obj["amount"]["den"], 1);
    }

    #[test]
    fn test_normalize_float_number() {
        let action = json!({
            "action": "borrow",
            "amount": 123.45
        });

        let result = normalize_amounts(&action, 0).unwrap();
        let obj = result.as_object().unwrap();
        // 123.45 = 12345/100 = 2469/20 after reduction
        assert_eq!(obj["amount"]["num"], 2469);
        assert_eq!(obj["amount"]["den"], 20);
    }

    #[test]
    fn test_zero_amount_error() {
        let action = json!({
            "action": "borrow",
            "amount": "0"
        });

        let result = normalize_amounts(&action, 0);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_eq!(err.code, transform_errors::NEGATIVE_AMOUNT);
    }

    #[test]
    fn test_negative_amount_error() {
        let action = json!({
            "action": "borrow",
            "amount": "-100"
        });

        let result = normalize_amounts(&action, 0);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_eq!(err.code, transform_errors::INVALID_AMOUNT);
    }

    #[test]
    fn test_invalid_amount_type() {
        let action = json!({
            "action": "borrow",
            "amount": true
        });

        let result = normalize_amounts(&action, 0);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_eq!(err.code, transform_errors::INVALID_AMOUNT);
        assert!(err.suggestion.is_some());
    }

    #[test]
    fn test_preserve_other_fields() {
        let action = json!({
            "action": "borrow",
            "amount": "100",
            "token": "WETH",
            "protocol": "aave",
            "extra_field": "preserved"
        });

        let result = normalize_amounts(&action, 0).unwrap();
        let obj = result.as_object().unwrap();
        assert_eq!(obj["extra_field"], "preserved");
        assert_eq!(obj["token"], "WETH");
    }
}