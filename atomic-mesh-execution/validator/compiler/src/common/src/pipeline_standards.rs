//! Pipeline Standards for Phase 3: Pipeline Integration
//! Defines standardized Unix pipeline compliance for all components

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Standardized exit codes for Unix pipeline compliance
#[derive(Debug, Clone, Copy)]
pub enum ExitCode {
    Success = 0,
    
    // Input/Output errors (1-9)
    InputError = 1,          // Failed to read stdin
    OutputError = 2,         // Failed to write stdout
    JsonParseError = 3,      // Malformed JSON input
    JsonSerializeError = 4,  // Failed to serialize output
    
    // Validation errors (10-19)
    ValidationError = 10,    // Input validation failed
    StructureError = 11,     // Invalid input structure
    MissingFieldError = 12,  // Required field missing
    TypeMismatchError = 13,  // Type validation failed
    
    // Processing errors (20-29)
    TransformError = 20,     // Action transformation failed
    ExpressionError = 21,    // Expression building failed
    AssemblyError = 22,      // Bundle assembly failed
    
    // Logic errors (30-39)
    ChainMismatchError = 30, // Chain consistency failed
    ConstraintError = 31,    // Constraint validation failed
    DependencyError = 32,    // Action dependency conflict
    
    // System errors (40-49)
    MemoryError = 40,        // Out of memory
    TimeoutError = 41,       // Operation timeout
    InternalError = 42,      // Unexpected internal error
}

impl ExitCode {
    pub fn as_i32(self) -> i32 {
        self as i32
    }
    
    pub fn description(self) -> &'static str {
        match self {
            ExitCode::Success => "Operation completed successfully",
            ExitCode::InputError => "Failed to read input from stdin",
            ExitCode::OutputError => "Failed to write output to stdout",
            ExitCode::JsonParseError => "Input JSON is malformed or invalid",
            ExitCode::JsonSerializeError => "Failed to serialize output JSON",
            ExitCode::ValidationError => "Input validation failed",
            ExitCode::StructureError => "Input structure is invalid",
            ExitCode::MissingFieldError => "Required field is missing",
            ExitCode::TypeMismatchError => "Field type does not match expected type",
            ExitCode::TransformError => "Action transformation failed",
            ExitCode::ExpressionError => "Expression building failed",
            ExitCode::AssemblyError => "Bundle assembly failed",
            ExitCode::ChainMismatchError => "Chain consistency validation failed",
            ExitCode::ConstraintError => "Constraint validation failed",
            ExitCode::DependencyError => "Action dependency conflict detected",
            ExitCode::MemoryError => "Out of memory",
            ExitCode::TimeoutError => "Operation timed out",
            ExitCode::InternalError => "Unexpected internal error",
        }
    }
}

/// Standardized pipeline metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PipelineMetadata {
    /// Component that processed this data
    pub component: String,
    
    /// Processing timestamp (ISO 8601)
    pub timestamp: String,
    
    /// Processing time in microseconds
    pub processing_time_us: u64,
    
    /// Component version
    pub version: String,
    
    /// Input data size in bytes
    pub input_size: usize,
    
    /// Output data size in bytes
    pub output_size: usize,
    
    /// Additional component-specific metadata
    pub extra: HashMap<String, serde_json::Value>,
}

impl PipelineMetadata {
    pub fn new(component: &str) -> Self {
        Self {
            component: component.to_string(),
            timestamp: chrono::Utc::now().to_rfc3339(),
            processing_time_us: 0,
            version: env!("CARGO_PKG_VERSION").to_string(),
            input_size: 0,
            output_size: 0,
            extra: HashMap::new(),
        }
    }
    
    pub fn with_timing(mut self, start_time: std::time::Instant) -> Self {
        self.processing_time_us = start_time.elapsed().as_micros() as u64;
        self
    }
    
    pub fn with_sizes(mut self, input_size: usize, output_size: usize) -> Self {
        self.input_size = input_size;
        self.output_size = output_size;
        self
    }
    
    pub fn with_extra(mut self, key: &str, value: serde_json::Value) -> Self {
        self.extra.insert(key.to_string(), value);
        self
    }
}

/// Standardized error format for pipeline communication
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StandardError {
    pub error: bool,
    pub component: String,
    pub code: String,
    pub message: String,
    pub exit_code: i32,
    pub timestamp: String,
    
    #[serde(skip_serializing_if = "Option::is_none")]
    pub context: Option<serde_json::Value>,
    
    #[serde(skip_serializing_if = "Option::is_none")]
    pub suggestion: Option<String>,
    
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<PipelineMetadata>,
}

impl StandardError {
    pub fn new(component: &str, code: &str, message: String, exit_code: ExitCode) -> Self {
        Self {
            error: true,
            component: component.to_string(),
            code: code.to_string(),
            message,
            exit_code: exit_code.as_i32(),
            timestamp: chrono::Utc::now().to_rfc3339(),
            context: None,
            suggestion: None,
            metadata: None,
        }
    }
    
    pub fn with_context(mut self, context: serde_json::Value) -> Self {
        self.context = Some(context);
        self
    }
    
    pub fn with_suggestion(mut self, suggestion: String) -> Self {
        self.suggestion = Some(suggestion);
        self
    }
    
    pub fn with_metadata(mut self, metadata: PipelineMetadata) -> Self {
        self.metadata = Some(metadata);
        self
    }
    
    /// Exit the process with standardized error output
    pub fn exit(self) -> ! {
        eprintln!("{}", serde_json::to_string_pretty(&self).unwrap());
        std::process::exit(self.exit_code);
    }
}

/// JSON streaming utilities for large inputs
pub struct JsonStreamer {
    buffer: String,
    max_size: usize,
}

impl JsonStreamer {
    pub fn new(max_size_mb: usize) -> Self {
        Self {
            buffer: String::new(),
            max_size: max_size_mb * 1024 * 1024,
        }
    }
    
    /// Read JSON from stdin with size limits
    pub fn read_stdin(&mut self) -> Result<serde_json::Value, StandardError> {
        use std::io::{self, Read};
        
        // Check if input exceeds size limit
        match io::stdin().read_to_string(&mut self.buffer) {
            Ok(_) => {
                if self.buffer.len() > self.max_size {
                    return Err(StandardError::new(
                        "json-streamer",
                        "INPUT_TOO_LARGE",
                        format!("Input size {} bytes exceeds limit of {} bytes", 
                                self.buffer.len(), self.max_size),
                        ExitCode::ValidationError
                    ).with_suggestion("Reduce input size or use chunked processing".to_string()));
                }
                
                // Parse JSON
                serde_json::from_str(&self.buffer).map_err(|e| {
                    StandardError::new(
                        "json-streamer",
                        "MALFORMED_JSON",
                        format!("JSON parse error: {}", e),
                        ExitCode::JsonParseError
                    ).with_context(serde_json::json!({
                        "input_size": self.buffer.len(),
                        "error_position": e.line()
                    }))
                })
            }
            Err(e) => {
                Err(StandardError::new(
                    "json-streamer",
                    "INPUT_READ_ERROR",
                    format!("Failed to read stdin: {}", e),
                    ExitCode::InputError
                ))
            }
        }
    }
    
    /// Write JSON to stdout with formatting
    pub fn write_stdout<T: Serialize>(&self, data: &T, pretty: bool) -> Result<(), StandardError> {
        let json_string = if pretty {
            serde_json::to_string_pretty(data)
        } else {
            serde_json::to_string(data)
        }.map_err(|e| {
            StandardError::new(
                "json-streamer",
                "SERIALIZE_ERROR",
                format!("Failed to serialize output: {}", e),
                ExitCode::JsonSerializeError
            )
        })?;
        
        println!("{}", json_string);
        Ok(())
    }
}

/// Component performance tracker
#[derive(Debug)]
pub struct PerformanceTracker {
    component: String,
    start_time: std::time::Instant,
    checkpoints: Vec<(String, std::time::Instant)>,
}

impl PerformanceTracker {
    pub fn new(component: &str) -> Self {
        Self {
            component: component.to_string(),
            start_time: std::time::Instant::now(),
            checkpoints: Vec::new(),
        }
    }
    
    pub fn checkpoint(&mut self, name: &str) {
        self.checkpoints.push((name.to_string(), std::time::Instant::now()));
    }
    
    pub fn total_duration_us(&self) -> u64 {
        self.start_time.elapsed().as_micros() as u64
    }
    
    pub fn generate_metadata(&self, input_size: usize, output_size: usize) -> PipelineMetadata {
        let mut metadata = PipelineMetadata::new(&self.component)
            .with_timing(self.start_time)
            .with_sizes(input_size, output_size);
        
        // Add checkpoint timings
        let mut checkpoint_data = serde_json::Map::new();
        for (name, time) in &self.checkpoints {
            let duration_us = time.duration_since(self.start_time).as_micros() as u64;
            checkpoint_data.insert(name.clone(), serde_json::Value::Number(duration_us.into()));
        }
        
        if !checkpoint_data.is_empty() {
            metadata.extra.insert("checkpoints_us".to_string(), 
                                serde_json::Value::Object(checkpoint_data));
        }
        
        metadata
    }
}