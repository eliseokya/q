//! Parse and validate stage (optimized for performance)

use serde_json::{Value, from_str};
use common::{CompilerError, PipelineData, Metadata};

#[inline]
pub fn process(input: &str) -> Result<PipelineData, CompilerError> {
    // Fast JSON parsing (optimized path)
    let json_value: Value = from_str(input).map_err(|e| {
        CompilerError::new(
            "monolithic-parse",
            "MALFORMED_JSON",
            format!("Failed to parse JSON: {}", e)
        )
    })?;

    // Inline validation and extraction for performance
    let obj = json_value.as_object().ok_or_else(|| {
        CompilerError::new(
            "monolithic-parse",
            "INVALID_STRUCTURE",
            "Root must be an object".to_string()
        )
    })?;

    // Fast path: Check required fields once
    if !obj.contains_key("path") && !obj.contains_key("actions") {
        return Err(CompilerError::new(
            "monolithic-parse",
            "MISSING_REQUIRED_FIELD",
            "Missing required field: 'path' or 'actions'".to_string()
        ));
    }

    // Extract data with pre-allocated structures
    let metadata = Metadata {
        opportunity_id: obj.get("opportunity_id")
            .and_then(|v| v.as_str())
            .unwrap_or("unknown")
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
            .and_then(|v| v.as_str())
            .map(|s| s.to_string()),
        confidence: obj.get("confidence")
            .and_then(|v| v.as_f64()),
    };

    // Pre-allocate actions vector if we know the size
    let actions = obj.get("path")
        .or_else(|| obj.get("actions"))
        .and_then(|v| v.as_array())
        .map(|arr| arr.clone());

    // Keep constraints as-is for minimal processing
    let constraints = obj.get("constraints")
        .cloned()
        .unwrap_or(Value::Object(serde_json::Map::new()));

    Ok(PipelineData {
        metadata,
        actions,
        typed_actions: None,
        expr: None,
        constraints,
    })
}