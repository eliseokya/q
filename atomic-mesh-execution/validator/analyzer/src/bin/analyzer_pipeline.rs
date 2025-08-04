//! CLI binary for running the analyzer in pipeline mode
//!
//! This binary integrates with the compiler via stdin/stdout for
//! the complete validation pipeline.

use analyzer::{PipelineBuilder, PipelineError};
use std::env;
use std::process;

fn main() {
    // Initialize logger
    env_logger::init();
    
    // Parse command line arguments
    let args: Vec<String> = env::args().collect();
    let mut performance_mode = "production";
    let mut verbose = false;
    
    for arg in args.iter().skip(1) {
        match arg.as_str() {
            "--development" => performance_mode = "development",
            "--strict" => performance_mode = "strict",
            "--verbose" | "-v" => verbose = true,
            "--help" | "-h" => {
                print_help();
                process::exit(0);
            }
            _ => {
                eprintln!("Unknown argument: {}", arg);
                print_help();
                process::exit(1);
            }
        }
    }
    
    // Build and run the pipeline
    let result = run_pipeline(performance_mode, verbose);
    
    match result {
        Ok(()) => {
            if verbose {
                eprintln!("Pipeline completed successfully");
            }
        }
        Err(e) => {
            eprintln!("Pipeline error: {}", e);
            process::exit(1);
        }
    }
}

fn run_pipeline(performance_mode: &str, verbose: bool) -> Result<(), PipelineError> {
    let mut pipeline = PipelineBuilder::new()
        .performance_mode(performance_mode)
        .verbose(verbose)
        .build()?;
    
    pipeline.run_blocking()
}

fn print_help() {
    println!("Atomic Mesh Analyzer Pipeline");
    println!();
    println!("Usage: analyzer_pipeline [OPTIONS]");
    println!();
    println!("Options:");
    println!("  --development    Use development performance mode (relaxed timing)");
    println!("  --strict         Use strict performance mode (fail on budget violations)");
    println!("  --verbose, -v    Enable verbose output");
    println!("  --help, -h       Show this help message");
    println!();
    println!("The analyzer reads JSON messages from stdin and writes responses to stdout.");
    println!();
    println!("Input message format:");
    println!("  {{\"type\": \"analyze_bundle\", \"id\": \"...\", \"bundle\": {{...}}}}");
    println!("  {{\"type\": \"status_request\"}}");
    println!("  {{\"type\": \"shutdown\"}}");
}