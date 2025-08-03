//! Extract and structure data from validated JSON

use serde_json::{Value, json};
use common::{CompilerError, PipelineData, Metadata};

/// Extract metadata, actions, and constraints from validated JSON
pub fn extract_data(json: &Value) -> Result<PipelineData, CompilerError> {
    let obj = json.as_object().unwrap(); // Already validated

    // Extract metadata
    let metadata = extract_metadata(obj);

    // Extract actions - preserve original structure for next component
    let actions = obj["path"].as_array().unwrap().clone(); // Already validated

    // Extract or default constraints
    let constraints = extract_constraints(obj);

    Ok(PipelineData {
        metadata,
        actions: Some(actions),
        typed_actions: None,
        expr: None,
        constraints,
    })
}

/// Extract metadata fields from the opportunity JSON
fn extract_metadata(obj: &serde_json::Map<String, Value>) -> Metadata {
    Metadata {
        opportunity_id: obj["opportunity_id"]
            .as_str()
            .unwrap_or_default()
            .to_string(),
        source_chain: obj.get("source_chain")
            .and_then(|v| v.as_str())
            .map(|s| s.to_string()),
        target_chain: obj.get("target_chain")
            .and_then(|v| v.as_str())
            .map(|s| s.to_string()),
        timestamp: obj.get("timestamp")
            .and_then(|v| v.as_str())
            .map(|s| s.to_string()),
        expected_profit: obj.get("expected_profit")
            .and_then(|v| {
                // Handle both string and number formats
                if let Some(s) = v.as_str() {
                    Some(s.to_string())
                } else if let Some(n) = v.as_f64() {
                    Some(n.to_string())
                } else if let Some(n) = v.as_u64() {
                    Some(n.to_string())
                } else {
                    None
                }
            }),
        confidence: obj.get("confidence")
            .and_then(|v| v.as_f64()),
    }
}

/// Extract constraints with comprehensive defaults
fn extract_constraints(obj: &serde_json::Map<String, Value>) -> Value {
    if let Some(constraints) = obj.get("constraints") {
        // Ensure it's an object and add defaults for missing fields
        if let Some(constraint_obj) = constraints.as_object() {
            let mut result = constraint_obj.clone();
            
            // Add default values for missing fields
            // Deadline: null means no deadline constraint
            if !result.contains_key("deadline") {
                result.insert("deadline".to_string(), Value::Null);
            }
            
            // Max gas: null means no gas limit
            if !result.contains_key("max_gas") {
                result.insert("max_gas".to_string(), Value::Null);
            }
            
            // Min balance: null means no minimum balance requirement
            if !result.contains_key("min_balance") {
                result.insert("min_balance".to_string(), Value::Null);
            }
            
            // Invariants: empty array means no invariants
            if !result.contains_key("invariants") {
                result.insert("invariants".to_string(), json!([]));
            }
            
            // Preserve any custom constraints
            Value::Object(result)
        } else {
            // If constraints is not an object, return default
            default_constraints()
        }
    } else {
        // No constraints provided, use defaults
        default_constraints()
    }
}

/// Default constraints object with all fields set to null/empty
fn default_constraints() -> Value {
    json!({
        "deadline": null,
        "max_gas": null,
        "min_balance": null,
        "invariants": []
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn test_extract_basic_data() {
        let json = json!({
            "opportunity_id": "test_123",
            "path": [
                {"action": "borrow", "amount": "100", "token": "WETH", "protocol": "aave"}
            ]
        });

        let result = extract_data(&json).unwrap();
        assert_eq!(result.metadata.opportunity_id, "test_123");
        assert_eq!(result.actions.unwrap().len(), 1);
        
        // Check default constraints
        let constraints = result.constraints.as_object().unwrap();
        assert!(constraints["deadline"].is_null());
        assert!(constraints["max_gas"].is_null());
        assert!(constraints["min_balance"].is_null());
        assert_eq!(constraints["invariants"], json!([]));
    }

    #[test]
    fn test_extract_with_all_metadata() {
        let json = json!({
            "opportunity_id": "test_123",
            "source_chain": "polygon",
            "target_chain": "arbitrum",
            "timestamp": "2024-08-03T12:34:56Z",
            "expected_profit": "500",
            "confidence": 0.95,
            "path": [{"action": "borrow", "amount": "100", "token": "WETH", "protocol": "aave"}]
        });

        let result = extract_data(&json).unwrap();
        assert_eq!(result.metadata.source_chain, Some("polygon".to_string()));
        assert_eq!(result.metadata.target_chain, Some("arbitrum".to_string()));
        assert_eq!(result.metadata.timestamp, Some("2024-08-03T12:34:56Z".to_string()));
        assert_eq!(result.metadata.expected_profit, Some("500".to_string()));
        assert_eq!(result.metadata.confidence, Some(0.95));
    }

    #[test]
    fn test_extract_numeric_profit() {
        let json = json!({
            "opportunity_id": "test",
            "expected_profit": 123.45,
            "path": [{"action": "borrow", "amount": "100", "token": "WETH", "protocol": "aave"}]
        });

        let result = extract_data(&json).unwrap();
        assert_eq!(result.metadata.expected_profit, Some("123.45".to_string()));
    }

    #[test]
    fn test_extract_with_partial_constraints() {
        let json = json!({
            "opportunity_id": "test",
            "path": [{"action": "borrow", "amount": "100", "token": "WETH", "protocol": "aave"}],
            "constraints": {
                "deadline": 20,
                "max_gas": 1000000
            }
        });

        let result = extract_data(&json).unwrap();
        let constraints = result.constraints.as_object().unwrap();
        assert_eq!(constraints["deadline"], 20);
        assert_eq!(constraints["max_gas"], 1000000);
        assert!(constraints["min_balance"].is_null()); // Default added
        assert_eq!(constraints["invariants"], json!([])); // Default added
    }

    #[test]
    fn test_extract_with_all_constraints() {
        let json = json!({
            "opportunity_id": "test",
            "path": [{"action": "borrow", "amount": "100", "token": "WETH", "protocol": "aave"}],
            "constraints": {
                "deadline": 20,
                "max_gas": 1000000,
                "min_balance": {
                    "token": "USDC",
                    "amount": "100"
                },
                "invariants": ["constant-product", "no-negative-balance"],
                "custom_constraint": "value" // Should be preserved
            }
        });

        let result = extract_data(&json).unwrap();
        let constraints = result.constraints.as_object().unwrap();
        assert_eq!(constraints["deadline"], 20);
        assert_eq!(constraints["max_gas"], 1000000);
        assert!(constraints["min_balance"].is_object());
        assert_eq!(constraints["invariants"].as_array().unwrap().len(), 2);
        assert_eq!(constraints["custom_constraint"], "value"); // Custom preserved
    }

    #[test]
    fn test_actions_preserved_exactly() {
        let json = json!({
            "opportunity_id": "test",
            "path": [
                {
                    "action": "swap",
                    "from": "WETH",
                    "to": "USDC",
                    "amount": "100",
                    "minOut": "150000",
                    "protocol": "uniswap",
                    "extra_field": "preserved"
                }
            ]
        });

        let result = extract_data(&json).unwrap();
        let actions = result.actions.unwrap();
        assert_eq!(actions[0]["extra_field"], "preserved");
    }
}