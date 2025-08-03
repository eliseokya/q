//! Parse and validate component - First stage of the compiler pipeline
//! Reads opportunity JSON from stdin, validates structure, and outputs normalized data

mod parser;
mod validator;
mod extractor;

use common::errors::{read_stdin, write_stdout, CompilerError, parse_errors};

fn main() {
    // Read input from stdin
    let input = match read_stdin() {
        Ok(data) => data,
        Err(e) => {
            CompilerError::new(
                "parse-and-validate",
                parse_errors::MALFORMED_JSON,
                format!("Failed to read input: {}", e)
            ).exit(1);
        }
    };

    // Parse JSON
    let json_value = match parser::parse_json(&input) {
        Ok(value) => value,
        Err(e) => e.exit(1),
    };

    // Validate structure
    if let Err(e) = validator::validate_structure(&json_value) {
        e.exit(2);
    }

    // Extract and structure data
    let pipeline_data = match extractor::extract_data(&json_value) {
        Ok(data) => data,
        Err(e) => e.exit(3),
    };

    // Write output to stdout
    if let Err(e) = write_stdout(&pipeline_data) {
        CompilerError::new(
            "parse-and-validate",
            "OUTPUT_ERROR",
            format!("Failed to write output: {}", e)
        ).exit(1);
    }
}