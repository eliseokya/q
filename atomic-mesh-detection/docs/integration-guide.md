# Integration Guide

## Execution System Integration

### Setup
1. Configure endpoints in configs/integration.toml
2. Run integration setup:
   ```bash
   ./scripts/deploy/setup-integration.sh
   ```

### Communication Protocol
- Primary: Unix domain sockets
- Backup: WebSocket
- Format: JSON

### Capability Synchronization
The detection system automatically syncs with execution capabilities:
- Supported protocols
- Supported bridges
- Gas models
- Constraints

### Feedback Loop
Execution results are processed to improve detection:
- Success/failure patterns
- Actual vs predicted profit
- Gas accuracy
- Timing analysis

## Monitoring Integration
See monitoring/dashboards/execution-integration.json
