//! Registry module for protocol and bridge configurations

pub mod protocol_registry;
pub mod loader;

pub use protocol_registry::ProtocolRegistry;
pub use loader::load_protocol_config;