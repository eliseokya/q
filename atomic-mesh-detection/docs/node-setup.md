# Node Setup Guide

## Requirements
- 16+ CPU cores per chain
- 32GB+ RAM per chain
- 2TB+ NVMe storage per chain
- 10Gbps+ network

## Installation

1. Build unified-reth:
   ```bash
   cd nodes/unified-reth
   cargo build --release
   ```

2. Initialize databases:
   ```bash
   ./scripts/deploy/init-databases.sh
   ```

3. Start nodes:
   ```bash
   ./scripts/deploy/setup-nodes.sh
   ```

## Configuration
See configs/chains/*.toml for chain-specific settings.

## Monitoring
Grafana dashboards available at http://localhost:3000
