//! Monolithic compiler - High-performance single-binary version
//! Chains all 4 pipeline stages in-memory without JSON serialization overhead

use common::{
    CompilerError,
    errors::{read_stdin, write_stdout},
};

// Include the processing modules directly (copied from components)
mod parse_stage;
mod transform_stage; 
mod build_stage;
mod assemble_stage;

fn main() {
    // Read input
    let input = match read_stdin() {
        Ok(data) => data,
        Err(e) => {
            CompilerError::new(
                "monolithic",
                "IO_ERROR", 
                format!("Failed to read input: {}", e)
            ).exit(1);
        }
    };

    // Stage 1: Parse and Validate (in-memory)
    let mut pipeline_data = match parse_stage::process(&input) {
        Ok(data) => data,
        Err(e) => e.exit(1),
    };

    // Stage 2: Transform Actions (in-memory) 
    if let Err(e) = transform_stage::process(&mut pipeline_data) {
        e.exit(2);
    }

    // Stage 3: Build Expression (in-memory)
    if let Err(e) = build_stage::process(&mut pipeline_data) {
        e.exit(3);
    }

    // Stage 4: Assemble Bundle (in-memory)
    let bundle = match assemble_stage::process(pipeline_data) {
        Ok(bundle) => bundle,
        Err(e) => e.exit(4),
    };

    // Write output
    if let Err(e) = write_stdout(&bundle) {
        CompilerError::new(
            "monolithic",
            "OUTPUT_ERROR",
            format!("Failed to write output: {}", e)
        ).exit(5);
    }
}