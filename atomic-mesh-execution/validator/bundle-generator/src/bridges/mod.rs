//! Bridge integration for cross-chain operations

pub mod types;
pub mod router;
pub mod registry;

pub use types::{Bridge, BridgeInfo, BridgeRoute, BridgeCapability, BridgeSelectionCriteria};
pub use router::BridgeRouter;
pub use registry::{BridgeRegistry, load_bridge_config};