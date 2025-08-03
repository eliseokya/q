# Atomic Mesh Detection System

High-performance arbitrage detection system using unified full nodes across 5 chains.

## Architecture

- **5 Full Nodes**: Direct access to Ethereum, Arbitrum, Polygon, Base, and Optimism
- **74 Detection Tools**: Unix philosophy - each tool does one thing well
- **30 Strategies**: Advanced arbitrage strategies from simple to complex
- **Sub-second Detection**: Direct mempool access, no RPC delays

## Quick Start

1. Install dependencies:
   ```bash
   make install
   ```

2. Start nodes:
   ```bash
   make run-nodes
   ```

3. Run detection pipeline:
   ```bash
   ./pipes/simple-arb.sh
   ```

## Components

- `nodes/`: Unified node infrastructure
- `extractors/`: Data extraction tools
- `analyzers/`: Analysis and opportunity detection
- `strategies/`: Arbitrage strategy implementations
- `integration/`: Interface with execution system

## Requirements

- 80-160GB RAM
- 6-8TB NVMe storage
- 32+ CPU cores
- 10Gbps+ network

See docs/ for detailed documentation.
