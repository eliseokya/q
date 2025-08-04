//! Hot-reload system for dynamic pattern updates
//! 
//! This module monitors the `maths/` folder for changes to Lean theorem files
//! and triggers pattern recompilation when changes are detected.

pub mod filesystem_watcher;
pub mod event_handler;

pub use filesystem_watcher::FilesystemWatcher;
pub use event_handler::{EventHandler, WatchEvent, HotReloadManager};