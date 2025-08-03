//! Structure validation for opportunity JSON

use serde_json::Value;
use common::{CompilerError, parse_errors};

/// Validate the required structure of opportunity JSON
pub fn validate_structure(json: &Value) -> Result<(), CompilerError> {
    // Must be an object
    let obj = json.as_object().ok_or_else(|| {
        CompilerError::new(
            "parse-and-validate",
            parse_errors::INVALID_TYPE,
            "Input must be a JSON object".to_string()
        )
        .with_context(serde_json::json!({
            "actual_type": json.type_name()
        }))
        .with_suggestion("Wrap your input in curly braces: { ... }".to_string())
    })?;

    // Check required fields
    validate_opportunity_id(obj)?;
    validate_path(obj)?;
    
    // Validate optional fields if present
    if obj.contains_key("constraints") {
        validate_constraints(&obj["constraints"])?;
    }
    
    if obj.contains_key("source_chain") {
        validate_chain_field(&obj["source_chain"], "source_chain")?;
    }
    
    if obj.contains_key("target_chain") {
        validate_chain_field(&obj["target_chain"], "target_chain")?;
    }

    Ok(())
}

/// Validate opportunity_id field
fn validate_opportunity_id(obj: &serde_json::Map<String, Value>) -> Result<(), CompilerError> {
    if !obj.contains_key("opportunity_id") {
        return Err(CompilerError::new(
            "parse-and-validate",
            parse_errors::MISSING_FIELD,
            "Missing required field: opportunity_id".to_string()
        )
        .with_suggestion("Add 'opportunity_id' field to identify the opportunity".to_string()));
    }

    // Validate it's a string
    let id = obj["opportunity_id"].as_str().ok_or_else(|| {
        CompilerError::new(
            "parse-and-validate",
            parse_errors::INVALID_TYPE,
            "Field 'opportunity_id' must be a string".to_string()
        )
        .with_context(serde_json::json!({
            "actual_type": obj["opportunity_id"].type_name()
        }))
    })?;

    // Validate it's not empty
    if id.trim().is_empty() {
        return Err(CompilerError::new(
            "parse-and-validate",
            parse_errors::INVALID_TYPE,
            "Field 'opportunity_id' cannot be empty".to_string()
        ));
    }

    Ok(())
}

/// Validate path field
fn validate_path(obj: &serde_json::Map<String, Value>) -> Result<(), CompilerError> {
    if !obj.contains_key("path") {
        return Err(CompilerError::new(
            "parse-and-validate",
            parse_errors::MISSING_FIELD,
            "Missing required field: path".to_string()
        )
        .with_suggestion("Add 'path' array containing the action sequence".to_string()));
    }

    // Validate path is an array
    let path = obj["path"].as_array().ok_or_else(|| {
        CompilerError::new(
            "parse-and-validate",
            parse_errors::INVALID_TYPE,
            "Field 'path' must be an array".to_string()
        )
        .with_context(serde_json::json!({
            "actual_type": obj["path"].type_name()
        }))
    })?;

    // Path must not be empty
    if path.is_empty() {
        return Err(CompilerError::new(
            "parse-and-validate",
            parse_errors::EMPTY_ACTIONS,
            "Path array cannot be empty".to_string()
        )
        .with_suggestion("Add at least one action to the path".to_string()));
    }

    // Validate each action
    for (index, action) in path.iter().enumerate() {
        validate_action(action, index)?;
    }

    Ok(())
}

/// Validate individual action
fn validate_action(action: &Value, index: usize) -> Result<(), CompilerError> {
    let action_obj = action.as_object().ok_or_else(|| {
        CompilerError::new(
            "parse-and-validate",
            parse_errors::INVALID_TYPE,
            format!("Action at index {} must be an object", index)
        )
        .with_context(serde_json::json!({
            "action_index": index,
            "actual_type": action.type_name()
        }))
    })?;

    // Check required action field
    if !action_obj.contains_key("action") {
        return Err(CompilerError::new(
            "parse-and-validate",
            parse_errors::MISSING_FIELD,
            format!("Action at index {} missing 'action' field", index)
        )
        .with_context(serde_json::json!({
            "action_index": index
        }))
        .with_suggestion("Each action must have an 'action' field specifying the type".to_string()));
    }

    // Validate action type is a string
    let action_type = action_obj["action"].as_str().ok_or_else(|| {
        CompilerError::new(
            "parse-and-validate",
            parse_errors::INVALID_TYPE,
            format!("Action type at index {} must be a string", index)
        )
        .with_context(serde_json::json!({
            "action_index": index,
            "actual_type": action_obj["action"].type_name()
        }))
    })?;

    // Validate action type is recognized
    let valid_actions = ["borrow", "repay", "swap", "bridge", "deposit", "withdraw"];
    if !valid_actions.contains(&action_type.to_lowercase().as_str()) {
        return Err(CompilerError::new(
            "parse-and-validate",
            parse_errors::INVALID_TYPE,
            format!("Unknown action type '{}' at index {}", action_type, index)
        )
        .with_context(serde_json::json!({
            "action_index": index,
            "action_type": action_type
        }))
        .with_suggestion(format!("Valid actions are: {}", valid_actions.join(", "))));
    }

    // Validate action-specific fields
    match action_type.to_lowercase().as_str() {
        "borrow" | "repay" | "deposit" | "withdraw" => {
            validate_field_exists(action_obj, "amount", index)?;
            validate_field_exists(action_obj, "token", index)?;
            validate_field_exists(action_obj, "protocol", index)?;
        },
        "swap" => {
            // Check for either old or new field names
            let has_from_to = action_obj.contains_key("from") && action_obj.contains_key("to");
            let has_token_in_out = action_obj.contains_key("tokenIn") && action_obj.contains_key("tokenOut");
            
            if !has_from_to && !has_token_in_out {
                return Err(CompilerError::new(
                    "parse-and-validate",
                    parse_errors::MISSING_FIELD,
                    format!("Swap at index {} must have token fields", index)
                )
                .with_context(serde_json::json!({
                    "action_index": index
                }))
                .with_suggestion("Add 'from'/'to' or 'tokenIn'/'tokenOut' fields".to_string()));
            }
            
            // Check amount fields
            if !action_obj.contains_key("amount") && !action_obj.contains_key("amountIn") {
                return Err(CompilerError::new(
                    "parse-and-validate",
                    parse_errors::MISSING_FIELD,
                    format!("Swap at index {} must have amount field", index)
                )
                .with_context(serde_json::json!({
                    "action_index": index
                }))
                .with_suggestion("Add 'amount' or 'amountIn' field".to_string()));
            }
            
            validate_field_exists(action_obj, "protocol", index)?;
        },
        "bridge" => {
            validate_field_exists(action_obj, "to", index)?;
            validate_field_exists(action_obj, "token", index)?;
            validate_field_exists(action_obj, "amount", index)?;
        },
        _ => {} // Already validated above
    }

    Ok(())
}

/// Validate a field exists
fn validate_field_exists(
    obj: &serde_json::Map<String, Value>, 
    field: &str, 
    action_index: usize
) -> Result<(), CompilerError> {
    if !obj.contains_key(field) {
        return Err(CompilerError::new(
            "parse-and-validate",
            parse_errors::MISSING_FIELD,
            format!("Action at index {} missing required field '{}'", action_index, field)
        )
        .with_context(serde_json::json!({
            "action_index": action_index,
            "missing_field": field,
            "action_type": obj.get("action").and_then(|v| v.as_str()).unwrap_or("unknown")
        })));
    }
    Ok(())
}

/// Validate chain field
fn validate_chain_field(value: &Value, field_name: &str) -> Result<(), CompilerError> {
    value.as_str().ok_or_else(|| {
        CompilerError::new(
            "parse-and-validate",
            parse_errors::INVALID_TYPE,
            format!("Field '{}' must be a string", field_name)
        )
        .with_context(serde_json::json!({
            "field": field_name,
            "actual_type": value.type_name()
        }))
    })?;
    Ok(())
}

/// Validate constraints object
fn validate_constraints(value: &Value) -> Result<(), CompilerError> {
    let constraints = value.as_object().ok_or_else(|| {
        CompilerError::new(
            "parse-and-validate",
            parse_errors::INVALID_TYPE,
            "Field 'constraints' must be an object".to_string()
        )
        .with_context(serde_json::json!({
            "actual_type": value.type_name()
        }))
    })?;

    // Validate known constraint types
    for (key, constraint_value) in constraints {
        match key.as_str() {
            "deadline" => {
                // Must be a positive number
                if !constraint_value.is_number() {
                    return Err(CompilerError::new(
                        "parse-and-validate",
                        parse_errors::INVALID_TYPE,
                        "Constraint 'deadline' must be a number".to_string()
                    )
                    .with_context(serde_json::json!({
                        "actual_type": constraint_value.type_name()
                    })));
                }
            },
            "max_gas" => {
                // Must be a positive number
                if !constraint_value.is_number() {
                    return Err(CompilerError::new(
                        "parse-and-validate",
                        parse_errors::INVALID_TYPE,
                        "Constraint 'max_gas' must be a number".to_string()
                    )
                    .with_context(serde_json::json!({
                        "actual_type": constraint_value.type_name()
                    })));
                }
            },
            "min_balance" => {
                // Must be an object with token and amount
                if !constraint_value.is_object() {
                    return Err(CompilerError::new(
                        "parse-and-validate",
                        parse_errors::INVALID_TYPE,
                        "Constraint 'min_balance' must be an object".to_string()
                    ));
                }
            },
            "invariants" => {
                // Must be an array
                if !constraint_value.is_array() {
                    return Err(CompilerError::new(
                        "parse-and-validate",
                        parse_errors::INVALID_TYPE,
                        "Constraint 'invariants' must be an array".to_string()
                    ));
                }
            },
            _ => {
                // Unknown constraint - just pass through
            }
        }
    }

    Ok(())
}

/// Helper trait to get JSON value type name
trait TypeName {
    fn type_name(&self) -> &'static str;
}

impl TypeName for Value {
    fn type_name(&self) -> &'static str {
        match self {
            Value::Null => "null",
            Value::Bool(_) => "boolean",
            Value::Number(_) => "number",
            Value::String(_) => "string",
            Value::Array(_) => "array",
            Value::Object(_) => "object",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn test_valid_minimal_structure() {
        let json = json!({
            "opportunity_id": "test_123",
            "path": [
                {"action": "borrow", "amount": "100", "token": "WETH", "protocol": "aave"}
            ]
        });
        assert!(validate_structure(&json).is_ok());
    }

    #[test]
    fn test_valid_complete_structure() {
        let json = json!({
            "opportunity_id": "test_123",
            "source_chain": "polygon",
            "target_chain": "arbitrum",
            "path": [
                {"action": "borrow", "amount": "100", "token": "WETH", "protocol": "aave"},
                {"action": "bridge", "to": "arbitrum", "token": "WETH", "amount": "100"},
                {"action": "swap", "from": "WETH", "to": "USDC", "amount": "100", "minOut": "150000", "protocol": "uniswap"}
            ],
            "constraints": {
                "deadline": 20,
                "max_gas": 1000000
            }
        });
        assert!(validate_structure(&json).is_ok());
    }

    #[test]
    fn test_missing_opportunity_id() {
        let json = json!({
            "path": [{"action": "borrow"}]
        });
        let result = validate_structure(&json);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().code, parse_errors::MISSING_FIELD);
    }

    #[test]
    fn test_empty_path() {
        let json = json!({
            "opportunity_id": "test",
            "path": []
        });
        let result = validate_structure(&json);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().code, parse_errors::EMPTY_ACTIONS);
    }

    #[test]
    fn test_invalid_action_type() {
        let json = json!({
            "opportunity_id": "test",
            "path": [{"action": "invalid_action"}]
        });
        let result = validate_structure(&json);
        assert!(result.is_err());
    }

    #[test]
    fn test_missing_action_fields() {
        let json = json!({
            "opportunity_id": "test",
            "path": [{"action": "borrow", "amount": "100"}]  // Missing token and protocol
        });
        let result = validate_structure(&json);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().code, parse_errors::MISSING_FIELD);
    }
}