#!/bin/bash
# Setup integration with execution system

set -e

echo "Setting up execution integration..."

# Verify execution system is accessible
if ! nc -z localhost 8888; then
  echo "ERROR: Execution system not accessible"
  exit 1
fi

# Configure integration endpoints
cat > configs/integration.toml << EOL
[execution]
feedback_endpoint = "unix:///tmp/execution-feedback.sock"
state_endpoint = "ws://localhost:8888"
gas_endpoint = "http://localhost:8080"

[detection]
feeder_endpoint = "unix:///tmp/detection-feeder.sock"
capability_check_interval = 300
EOL

# Test integration
../tools/execution-tester --quick

echo "Integration setup complete"
