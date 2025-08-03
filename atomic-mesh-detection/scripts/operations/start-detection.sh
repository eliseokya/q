#!/bin/bash
# Start the detection system

set -e

echo "Starting atomic-mesh-detection..."

# Start monitoring
echo "Starting monitoring services..."
monitoring/latency-monitor --daemon &
monitoring/profit-monitor --daemon &
monitoring/failure-monitor --daemon &

# Start core detection pipelines
echo "Starting detection pipelines..."
pipes/simple-arb.sh &
pipes/cross-chain-arb.sh &
pipes/flash-loan-arb.sh &

# Start integration services
echo "Starting integration services..."
integration/execution-monitor --continuous &
integration/feedback-receiver --process &

# Save PIDs
mkdir -p .pids
jobs -p > .pids/detection.pids

echo "Detection system started"
echo "PIDs saved to .pids/detection.pids"
