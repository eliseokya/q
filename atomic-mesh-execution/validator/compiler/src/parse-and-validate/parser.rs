//! JSON parsing functionality with detailed error reporting

use serde_json::Value;
use common::{CompilerError, parse_errors};

/// Parse JSON from string input with comprehensive error reporting
pub fn parse_json(input: &str) -> Result<Value, CompilerError> {
    // Check for empty input
    if input.trim().is_empty() {
        return Err(CompilerError::new(
            "parse-and-validate",
            parse_errors::MALFORMED_JSON,
            "Empty input provided".to_string()
        )
        .with_suggestion("Provide valid JSON input via stdin".to_string()));
    }

    // Attempt to parse JSON
    serde_json::from_str(input).map_err(|e| {
        let mut error = CompilerError::new(
            "parse-and-validate",
            parse_errors::MALFORMED_JSON,
            format!("Invalid JSON syntax: {}", e)
        );

        // Add context about error location
        error = error.with_context(serde_json::json!({
            "error_position": {
                "line": e.line(),
                "column": e.column()
            },
            "input_length": input.len(),
            "input_preview": get_error_preview(input, e.line(), e.column())
        }));

        // Add helpful suggestions based on common errors
        error = match classify_json_error(&e) {
            JsonErrorType::MissingQuotes => {
                error.with_suggestion("Ensure all string values are enclosed in double quotes".to_string())
            },
            JsonErrorType::TrailingComma => {
                error.with_suggestion("Remove trailing comma after the last element in arrays or objects".to_string())
            },
            JsonErrorType::InvalidEscape => {
                error.with_suggestion("Use valid escape sequences: \\\" for quotes, \\\\ for backslash".to_string())
            },
            JsonErrorType::UnexpectedToken => {
                error.with_suggestion("Check for missing commas, brackets, or quotes".to_string())
            },
            JsonErrorType::Other => {
                error.with_suggestion("Validate JSON using an online validator for detailed errors".to_string())
            }
        };

        error
    })
}

/// Get a preview of the error location in the input
fn get_error_preview(input: &str, line: usize, column: usize) -> String {
    let lines: Vec<&str> = input.lines().collect();
    
    if line == 0 || line > lines.len() {
        return String::from("<unable to determine error location>");
    }

    let error_line = lines[line - 1];
    let start = column.saturating_sub(20);
    let end = (column + 20).min(error_line.len());
    
    let preview = &error_line[start..end];
    let pointer_pos = column.saturating_sub(start);
    let pointer = format!("{}^", " ".repeat(pointer_pos));
    
    format!("{}\n{}", preview, pointer)
}

/// Classify JSON parsing errors for better suggestions
enum JsonErrorType {
    MissingQuotes,
    TrailingComma,
    InvalidEscape,
    UnexpectedToken,
    Other,
}

fn classify_json_error(error: &serde_json::Error) -> JsonErrorType {
    let error_str = error.to_string().to_lowercase();
    
    if error_str.contains("expected value") && error_str.contains("found") {
        JsonErrorType::MissingQuotes
    } else if error_str.contains("trailing comma") {
        JsonErrorType::TrailingComma
    } else if error_str.contains("escape") {
        JsonErrorType::InvalidEscape
    } else if error_str.contains("unexpected") {
        JsonErrorType::UnexpectedToken
    } else {
        JsonErrorType::Other
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_valid_json() {
        let input = r#"{"test": "value", "number": 123}"#;
        let result = parse_json(input);
        assert!(result.is_ok());
        
        let value = result.unwrap();
        assert_eq!(value["test"], "value");
        assert_eq!(value["number"], 123);
    }

    #[test]
    fn test_empty_input() {
        let input = "";
        let result = parse_json(input);
        assert!(result.is_err());
        
        let err = result.unwrap_err();
        assert_eq!(err.code, parse_errors::MALFORMED_JSON);
        assert!(err.message.contains("Empty input"));
    }

    #[test]
    fn test_invalid_json_missing_quotes() {
        let input = r#"{"test": invalid}"#;
        let result = parse_json(input);
        assert!(result.is_err());
        
        let err = result.unwrap_err();
        assert_eq!(err.code, parse_errors::MALFORMED_JSON);
        assert!(err.suggestion.is_some());
    }

    #[test]
    fn test_invalid_json_trailing_comma() {
        let input = r#"{"test": "value",}"#;
        let result = parse_json(input);
        assert!(result.is_err());
    }

    #[test]
    fn test_complex_nested_json() {
        let input = r#"{
            "opportunity": {
                "id": "123",
                "path": [
                    {"action": "borrow", "amount": 100},
                    {"action": "swap", "amounts": [1, 2, 3]}
                ]
            }
        }"#;
        
        let result = parse_json(input);
        assert!(result.is_ok());
        
        let value = result.unwrap();
        assert_eq!(value["opportunity"]["id"], "123");
        assert_eq!(value["opportunity"]["path"][0]["action"], "borrow");
    }
}