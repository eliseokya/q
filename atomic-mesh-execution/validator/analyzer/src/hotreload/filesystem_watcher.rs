//! Filesystem watcher for monitoring changes to Lean theorem files
//! 
//! Watches the `maths/` directory for changes to `.lean` files and triggers
//! pattern recompilation when theorems are added or modified.

use std::path::{Path, PathBuf};
use std::sync::mpsc::{channel, Receiver, Sender};
use std::thread;
use std::time::Duration;
use std::fs;
use std::collections::HashMap;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum WatchError {
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),
    #[error("Failed to start watcher thread")]
    ThreadError,
    #[error("Path not found: {0}")]
    PathNotFound(String),
}

/// Events that can occur in the filesystem
#[derive(Debug, Clone)]
pub enum FileEvent {
    /// A new file was created
    Created(PathBuf),
    /// An existing file was modified
    Modified(PathBuf),
    /// A file was deleted
    Deleted(PathBuf),
}

/// Configuration for the filesystem watcher
#[derive(Debug, Clone)]
pub struct WatcherConfig {
    /// Root directory to watch (typically `maths/`)
    pub watch_root: PathBuf,
    /// File extensions to monitor
    pub extensions: Vec<String>,
    /// Polling interval in milliseconds
    pub poll_interval_ms: u64,
    /// Whether to watch subdirectories recursively
    pub recursive: bool,
}

impl Default for WatcherConfig {
    fn default() -> Self {
        Self {
            watch_root: PathBuf::from("maths"),
            extensions: vec!["lean".to_string()],
            poll_interval_ms: 1000, // 1 second
            recursive: true,
        }
    }
}

/// Filesystem watcher that monitors for changes to Lean files
pub struct FilesystemWatcher {
    config: WatcherConfig,
    sender: Sender<FileEvent>,
    receiver: Receiver<FileEvent>,
    file_states: HashMap<PathBuf, fs::Metadata>,
    running: bool,
}

impl FilesystemWatcher {
    /// Create a new filesystem watcher with default configuration
    pub fn new() -> Result<Self, WatchError> {
        Self::with_config(WatcherConfig::default())
    }

    /// Create a new filesystem watcher with custom configuration
    pub fn with_config(config: WatcherConfig) -> Result<Self, WatchError> {
        // Verify the watch root exists
        if !config.watch_root.exists() {
            return Err(WatchError::PathNotFound(
                config.watch_root.display().to_string()
            ));
        }

        let (sender, receiver) = channel();
        
        Ok(Self {
            config,
            sender,
            receiver,
            file_states: HashMap::new(),
            running: false,
        })
    }

    /// Start watching for file changes
    pub fn start(&mut self) -> Result<(), WatchError> {
        if self.running {
            return Ok(());
        }

        self.running = true;
        
        // Initial scan to populate file states
        self.scan_directory(&self.config.watch_root.clone())?;
        
        // Start the watching thread
        let config = self.config.clone();
        let sender = self.sender.clone();
        let mut file_states = self.file_states.clone();
        
        thread::spawn(move || {
            loop {
                // Check for changes
                if let Ok(events) = Self::check_for_changes(&config, &mut file_states) {
                    for event in events {
                        if sender.send(event).is_err() {
                            // Receiver dropped, exit thread
                            break;
                        }
                    }
                }
                
                thread::sleep(Duration::from_millis(config.poll_interval_ms));
            }
        });
        
        Ok(())
    }

    /// Stop watching for file changes
    pub fn stop(&mut self) {
        self.running = false;
    }

    /// Get the next file event (non-blocking)
    pub fn try_recv_event(&self) -> Option<FileEvent> {
        self.receiver.try_recv().ok()
    }

    /// Get the next file event (blocking)
    pub fn recv_event(&self) -> Result<FileEvent, WatchError> {
        self.receiver.recv()
            .map_err(|_| WatchError::ThreadError)
    }

    /// Check if the watcher is running
    pub fn is_running(&self) -> bool {
        self.running
    }

    /// Scan a directory and populate file states
    fn scan_directory(&mut self, path: &Path) -> Result<(), WatchError> {
        if !path.is_dir() {
            return Ok(());
        }

        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let path = entry.path();
            
            if path.is_dir() && self.config.recursive {
                self.scan_directory(&path)?;
            } else if self.should_watch_file(&path) {
                if let Ok(metadata) = fs::metadata(&path) {
                    self.file_states.insert(path, metadata);
                }
            }
        }
        
        Ok(())
    }

    /// Check if a file should be watched based on extension
    fn should_watch_file(&self, path: &Path) -> bool {
        if let Some(ext) = path.extension() {
            if let Some(ext_str) = ext.to_str() {
                return self.config.extensions.contains(&ext_str.to_string());
            }
        }
        false
    }

    /// Check for changes in the watched directory
    fn check_for_changes(
        config: &WatcherConfig,
        file_states: &mut HashMap<PathBuf, fs::Metadata>
    ) -> Result<Vec<FileEvent>, WatchError> {
        let mut events = Vec::new();
        let mut current_files = HashMap::new();
        
        // Scan current state
        Self::scan_directory_static(&config.watch_root, config, &mut current_files)?;
        
        // Check for new and modified files
        for (path, metadata) in &current_files {
            match file_states.get(path) {
                Some(old_metadata) => {
                    // Check if modified
                    if old_metadata.modified()? != metadata.modified()? {
                        events.push(FileEvent::Modified(path.clone()));
                    }
                }
                None => {
                    // New file
                    events.push(FileEvent::Created(path.clone()));
                }
            }
        }
        
        // Check for deleted files
        let deleted_files: Vec<PathBuf> = file_states.keys()
            .filter(|path| !current_files.contains_key(*path))
            .cloned()
            .collect();
        
        for path in deleted_files {
            events.push(FileEvent::Deleted(path.clone()));
            file_states.remove(&path);
        }
        
        // Update file states
        *file_states = current_files;
        
        Ok(events)
    }

    /// Static version of scan_directory for use in thread
    fn scan_directory_static(
        path: &Path,
        config: &WatcherConfig,
        files: &mut HashMap<PathBuf, fs::Metadata>
    ) -> Result<(), WatchError> {
        if !path.is_dir() {
            return Ok(());
        }

        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let path = entry.path();
            
            if path.is_dir() && config.recursive {
                Self::scan_directory_static(&path, config, files)?;
            } else if Self::should_watch_file_static(&path, &config.extensions) {
                if let Ok(metadata) = fs::metadata(&path) {
                    files.insert(path, metadata);
                }
            }
        }
        
        Ok(())
    }

    /// Static version of should_watch_file
    fn should_watch_file_static(path: &Path, extensions: &[String]) -> bool {
        if let Some(ext) = path.extension() {
            if let Some(ext_str) = ext.to_str() {
                return extensions.contains(&ext_str.to_string());
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::{self, File};
    use std::io::Write;
    use tempfile::TempDir;

    #[test]
    fn test_filesystem_watcher_creation() {
        // Create a temporary directory
        let temp_dir = TempDir::new().unwrap();
        let config = WatcherConfig {
            watch_root: temp_dir.path().to_path_buf(),
            ..Default::default()
        };
        
        let watcher = FilesystemWatcher::with_config(config).unwrap();
        assert!(!watcher.is_running());
    }

    #[test]
    fn test_file_detection() {
        // Create a temporary directory
        let temp_dir = TempDir::new().unwrap();
        let config = WatcherConfig {
            watch_root: temp_dir.path().to_path_buf(),
            poll_interval_ms: 100, // Fast polling for test
            ..Default::default()
        };
        
        let mut watcher = FilesystemWatcher::with_config(config).unwrap();
        watcher.start().unwrap();
        
        // Create a new Lean file
        let file_path = temp_dir.path().join("test.lean");
        let mut file = File::create(&file_path).unwrap();
        writeln!(file, "theorem test : True := by simp").unwrap();
        
        // Wait for detection
        thread::sleep(Duration::from_millis(200));
        
        // Check for created event
        let event = watcher.try_recv_event();
        assert!(event.is_some());
        
        if let Some(FileEvent::Created(path)) = event {
            assert_eq!(path.file_name().unwrap(), "test.lean");
        } else {
            panic!("Expected Created event");
        }
        
        watcher.stop();
    }
}