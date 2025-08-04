//! Bundle Generator CLI
//! 
//! Reads analysis results from stdin and outputs execution bundles to stdout

use std::io::{self, Read};
use std::path::Path;
use bundle_generator::{BundleGenerator, Result, AnalysisResult};

fn main() -> Result<()> {
    // Initialize logging
    env_logger::init();
    
    // Load configuration
    let config_path = Path::new("config/protocols.yaml");
    let generator = BundleGenerator::new(config_path)?;
    
    // Read analysis result from stdin
    let mut input = String::new();
    io::stdin().read_to_string(&mut input)?;
    
    // Parse analysis result
    let analysis: AnalysisResult = serde_json::from_str(&input)
        .map_err(|e| bundle_generator::BundleGeneratorError::ConfigError(
            format!("Failed to parse input: {}", e)
        ))?;
    
    // Generate execution bundle
    let bundle = generator.generate(analysis)?;
    
    // Output to stdout
    let output = serde_json::to_string_pretty(&bundle)
        .map_err(|e| bundle_generator::BundleGeneratorError::EncodingError(
            format!("Failed to serialize output: {}", e)
        ))?;
    
    println!("{}", output);
    
    Ok(())
}
