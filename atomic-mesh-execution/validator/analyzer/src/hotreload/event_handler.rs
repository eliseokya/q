//! Event handler for processing filesystem change events
//! 
//! Handles file change events from the filesystem watcher and triggers
//! appropriate actions like pattern recompilation.

use super::filesystem_watcher::FileEvent;
use crate::pattern_scanner::LeanParser;
use crate::pattern_compiler::LeanToPatternCompiler;
use crate::engine::StaticPatternLibrary;
use std::path::PathBuf;
use std::sync::{Arc, RwLock};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum EventError {
    #[error("Failed to process file: {0}")]
    ProcessingError(String),
    #[error("Pattern compilation failed: {0}")]
    CompilationError(String),
    #[error("Library update failed: {0}")]
    LibraryUpdateError(String),
}

/// High-level watch events that combine file events with processing
#[derive(Debug, Clone)]
pub enum WatchEvent {
    /// New theorem detected and compiled
    TheoremAdded {
        file: PathBuf,
        theorem_count: usize,
    },
    /// Existing theorem modified and recompiled
    TheoremModified {
        file: PathBuf,
        theorem_count: usize,
    },
    /// Theorem file removed
    TheoremRemoved {
        file: PathBuf,
    },
    /// Error during processing
    ProcessingError {
        file: PathBuf,
        error: String,
    },
}

/// Event handler that processes filesystem events
pub struct EventHandler {
    /// Pattern library to update (wrapped in Arc<RwLock> for thread safety)
    pattern_library: Arc<RwLock<StaticPatternLibrary>>,
    /// Lean file parser
    lean_parser: LeanParser,
    /// Pattern compiler
    pattern_compiler: LeanToPatternCompiler,
}

impl EventHandler {
    /// Create a new event handler
    pub fn new(pattern_library: Arc<RwLock<StaticPatternLibrary>>) -> Self {
        Self {
            pattern_library,
            lean_parser: LeanParser::new(),
            pattern_compiler: LeanToPatternCompiler::new(),
        }
    }

    /// Process a file event and return a high-level watch event
    pub fn process_event(&mut self, event: FileEvent) -> WatchEvent {
        match event {
            FileEvent::Created(path) => self.handle_file_created(path),
            FileEvent::Modified(path) => self.handle_file_modified(path),
            FileEvent::Deleted(path) => self.handle_file_deleted(path),
        }
    }

    /// Handle a newly created Lean file
    fn handle_file_created(&mut self, path: PathBuf) -> WatchEvent {
        match self.process_lean_file(&path) {
            Ok(theorem_count) => WatchEvent::TheoremAdded {
                file: path,
                theorem_count,
            },
            Err(e) => WatchEvent::ProcessingError {
                file: path,
                error: e.to_string(),
            },
        }
    }

    /// Handle a modified Lean file
    fn handle_file_modified(&mut self, path: PathBuf) -> WatchEvent {
        match self.process_lean_file(&path) {
            Ok(theorem_count) => WatchEvent::TheoremModified {
                file: path,
                theorem_count,
            },
            Err(e) => WatchEvent::ProcessingError {
                file: path,
                error: e.to_string(),
            },
        }
    }

    /// Handle a deleted Lean file
    fn handle_file_deleted(&mut self, path: PathBuf) -> WatchEvent {
        // Remove patterns from this file from the library
        if let Ok(mut library) = self.pattern_library.write() {
            library.remove_patterns_from_file(&path);
        }
        
        WatchEvent::TheoremRemoved { file: path }
    }

    /// Process a Lean file and update the pattern library
    fn process_lean_file(&mut self, path: &PathBuf) -> Result<usize, EventError> {
        // Parse the Lean file
        let theorems = self.lean_parser.parse_lean_file(path)
            .map_err(|e| EventError::ProcessingError(
                format!("Failed to parse {}: {}", path.display(), e)
            ))?;
        
        let theorem_count = theorems.len();
        
        // Convert ExtractedTheorem to Theorem and compile to patterns
        let mut patterns = Vec::new();
        let mut database = crate::pattern_scanner::TheoremDatabase::new();
        
        for extracted_theorem in theorems {
            if let Ok(theorem_id) = database.add_theorem(extracted_theorem.clone()) {
                // Get the converted theorem from the database
                if let Some(theorem) = database.get_theorem(&theorem_id) {
                    match self.pattern_compiler.compile_theorem(theorem) {
                        Ok(pattern) => patterns.push(pattern),
                        Err(e) => {
                            // Log error but continue with other theorems
                            eprintln!("Warning: Failed to compile theorem {}: {}", theorem.name, e);
                        }
                    }
                }
            }
        }
        
        // Update the pattern library
        if let Ok(mut library) = self.pattern_library.write() {
            // Remove old patterns from this file
            library.remove_patterns_from_file(path);
            
            // Add new patterns
            for pattern in patterns {
                library.add_pattern(pattern);
            }
        } else {
            return Err(EventError::LibraryUpdateError(
                "Failed to acquire write lock on pattern library".to_string()
            ));
        }
        
        Ok(theorem_count)
    }

    /// Get a reference to the pattern library
    pub fn pattern_library(&self) -> Arc<RwLock<StaticPatternLibrary>> {
        self.pattern_library.clone()
    }
}

/// Integration with the analyzer engine for hot-reload
pub struct HotReloadManager {
    watcher: super::filesystem_watcher::FilesystemWatcher,
    handler: EventHandler,
    event_log: Vec<WatchEvent>,
}

impl HotReloadManager {
    /// Create a new hot-reload manager
    pub fn new(
        pattern_library: Arc<RwLock<StaticPatternLibrary>>,
        config: super::filesystem_watcher::WatcherConfig,
    ) -> Result<Self, super::filesystem_watcher::WatchError> {
        let watcher = super::filesystem_watcher::FilesystemWatcher::with_config(config)?;
        let handler = EventHandler::new(pattern_library);
        
        Ok(Self {
            watcher,
            handler,
            event_log: Vec::new(),
        })
    }

    /// Start the hot-reload system
    pub fn start(&mut self) -> Result<(), super::filesystem_watcher::WatchError> {
        self.watcher.start()
    }

    /// Process pending file events
    pub fn process_events(&mut self) -> Vec<WatchEvent> {
        let mut events = Vec::new();
        
        // Process all pending file events
        while let Some(file_event) = self.watcher.try_recv_event() {
            let watch_event = self.handler.process_event(file_event);
            events.push(watch_event.clone());
            self.event_log.push(watch_event);
        }
        
        events
    }

    /// Get the event log
    pub fn event_log(&self) -> &[WatchEvent] {
        &self.event_log
    }

    /// Clear the event log
    pub fn clear_event_log(&mut self) {
        self.event_log.clear();
    }

    /// Stop the hot-reload system
    pub fn stop(&mut self) {
        self.watcher.stop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;
    use std::fs::{self, File};
    use std::io::Write;

    #[test]
    fn test_event_handler_creation() {
        let pattern_library = Arc::new(RwLock::new(
            StaticPatternLibrary::new()
        ));
        let handler = EventHandler::new(pattern_library);
        assert!(handler.pattern_library.read().is_ok());
    }

    #[test]
    fn test_hot_reload_manager() {
        let temp_dir = TempDir::new().unwrap();
        let pattern_library = Arc::new(RwLock::new(
            StaticPatternLibrary::new()
        ));
        
        let config = super::super::filesystem_watcher::WatcherConfig {
            watch_root: temp_dir.path().to_path_buf(),
            poll_interval_ms: 100,
            ..Default::default()
        };
        
        let mut manager = HotReloadManager::new(pattern_library, config).unwrap();
        manager.start().unwrap();
        
        // Create a test Lean file
        let file_path = temp_dir.path().join("test_theorem.lean");
        let mut file = File::create(&file_path).unwrap();
        writeln!(file, "theorem test_atomicity : True := by simp").unwrap();
        
        // Wait and process events
        std::thread::sleep(std::time::Duration::from_millis(200));
        let events = manager.process_events();
        
        // Should have detected the new file
        assert!(!events.is_empty());
        
        manager.stop();
    }
}