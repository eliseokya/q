//! Integration module for compiler and proof verifier pipeline

pub mod compiler_interface;
pub mod pipeline_manager;

pub use compiler_interface::{CompilerInterface, CompilerMessage};
pub use pipeline_manager::{PipelineManager, PipelineConfig, PipelineBuilder, PipelineError};