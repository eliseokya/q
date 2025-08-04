//! Pipeline manager for orchestrating the full validation pipeline
//!
//! This module manages the complete flow from compiler to proof verifier,
//! handling configuration, error recovery, and monitoring.

use crate::engine::AnalyzerEngine;
use crate::integration::CompilerInterface;
use crate::PerformanceBudget;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use thiserror::Error;
use tokio::sync::mpsc;

#[derive(Error, Debug)]
pub enum PipelineError {
    #[error("Configuration error: {0}")]
    Configuration(String),
    
    #[error("Analyzer initialization failed: {0}")]
    AnalyzerInit(String),
    
    #[error("Interface error: {0}")]
    Interface(#[from] super::compiler_interface::InterfaceError),
    
    #[error("Pipeline interrupted")]
    Interrupted,
}

/// Configuration for the pipeline
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PipelineConfig {
    /// Performance mode: "production", "development", or "strict"
    pub performance_mode: String,
    
    /// Enable detailed logging
    pub verbose: bool,
    
    /// Maximum number of bundles to process (0 = unlimited)
    pub max_bundles: usize,
    
    /// Output metrics every N bundles
    pub metrics_interval: usize,
    
    /// Pattern library path (optional override)
    pub pattern_library_path: Option<PathBuf>,
}

impl Default for PipelineConfig {
    fn default() -> Self {
        Self {
            performance_mode: "production".to_string(),
            verbose: false,
            max_bundles: 0,
            metrics_interval: 1000,
            pattern_library_path: None,
        }
    }
}

/// Manages the complete analyzer pipeline
pub struct PipelineManager {
    config: PipelineConfig,
    analyzer: Option<AnalyzerEngine>,
}

impl PipelineManager {
    /// Create a new pipeline manager
    pub fn new(config: PipelineConfig) -> Self {
        Self {
            config,
            analyzer: None,
        }
    }
    
    /// Initialize the pipeline
    pub fn initialize(&mut self) -> Result<(), PipelineError> {
        // Create analyzer
        let mut analyzer = AnalyzerEngine::new()
            .map_err(|e| PipelineError::AnalyzerInit(e.to_string()))?;
        
        // Set performance mode
        match self.config.performance_mode.as_str() {
            "production" => analyzer.set_performance_budget(PerformanceBudget::default_budget()),
            "development" => analyzer.set_performance_budget(PerformanceBudget::development_budget()),
            "strict" => {
                analyzer.set_performance_budget(PerformanceBudget::strict_budget());
                analyzer.enable_strict_performance_mode();
            }
            mode => return Err(PipelineError::Configuration(
                format!("Invalid performance mode: {}", mode)
            )),
        }
        
        self.analyzer = Some(analyzer);
        Ok(())
    }
    
    /// Run the pipeline in blocking mode (for CLI usage)
    pub fn run_blocking(&mut self) -> Result<(), PipelineError> {
        let analyzer = self.analyzer.take()
            .ok_or_else(|| PipelineError::Configuration("Pipeline not initialized".to_string()))?;
        
        let mut interface = CompilerInterface::new(analyzer);
        
        if self.config.verbose {
            eprintln!("Pipeline started in {} mode", self.config.performance_mode);
            eprintln!("Reading from stdin, writing to stdout...");
        }
        
        interface.run()?;
        
        Ok(())
    }
    
    /// Run the pipeline asynchronously (for server usage)
    pub async fn run_async(&mut self, _shutdown: mpsc::Receiver<()>) -> Result<(), PipelineError> {
        // This would be implemented for async server mode
        // For now, we'll focus on the blocking CLI mode
        todo!("Async mode not yet implemented")
    }
    
    /// Get current pipeline statistics
    pub fn get_statistics(&self) -> PipelineStatistics {
        if let Some(analyzer) = &self.analyzer {
            let metrics_report = analyzer.get_metrics_report();
            PipelineStatistics {
                patterns_loaded: analyzer.get_pattern_count(),
                metrics_report,
            }
        } else {
            PipelineStatistics {
                patterns_loaded: 0,
                metrics_report: "Pipeline not initialized".to_string(),
            }
        }
    }
}

/// Statistics about the pipeline
#[derive(Debug, Clone, Serialize)]
pub struct PipelineStatistics {
    pub patterns_loaded: usize,
    pub metrics_report: String,
}

/// Builder pattern for PipelineManager
pub struct PipelineBuilder {
    config: PipelineConfig,
}

impl PipelineBuilder {
    /// Create a new builder
    pub fn new() -> Self {
        Self {
            config: PipelineConfig::default(),
        }
    }
    
    /// Set performance mode
    pub fn performance_mode(mut self, mode: &str) -> Self {
        self.config.performance_mode = mode.to_string();
        self
    }
    
    /// Enable verbose logging
    pub fn verbose(mut self, verbose: bool) -> Self {
        self.config.verbose = verbose;
        self
    }
    
    /// Set maximum bundles to process
    pub fn max_bundles(mut self, max: usize) -> Self {
        self.config.max_bundles = max;
        self
    }
    
    /// Set metrics interval
    pub fn metrics_interval(mut self, interval: usize) -> Self {
        self.config.metrics_interval = interval;
        self
    }
    
    /// Set pattern library path
    pub fn pattern_library_path(mut self, path: PathBuf) -> Self {
        self.config.pattern_library_path = Some(path);
        self
    }
    
    /// Build the pipeline manager
    pub fn build(self) -> Result<PipelineManager, PipelineError> {
        let mut manager = PipelineManager::new(self.config);
        manager.initialize()?;
        Ok(manager)
    }
}

impl Default for PipelineBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_pipeline_config_default() {
        let config = PipelineConfig::default();
        assert_eq!(config.performance_mode, "production");
        assert!(!config.verbose);
        assert_eq!(config.max_bundles, 0);
    }
    
    #[test]
    fn test_pipeline_builder() {
        let manager = PipelineBuilder::new()
            .performance_mode("development")
            .verbose(true)
            .max_bundles(100)
            .metrics_interval(50)
            .build();
        
        assert!(manager.is_ok());
        let manager = manager.unwrap();
        assert_eq!(manager.config.performance_mode, "development");
        assert!(manager.config.verbose);
        assert_eq!(manager.config.max_bundles, 100);
    }
    
    #[test]
    fn test_invalid_performance_mode() {
        let mut manager = PipelineManager::new(PipelineConfig {
            performance_mode: "invalid".to_string(),
            ..Default::default()
        });
        
        let result = manager.initialize();
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("Invalid performance mode"));
    }
}