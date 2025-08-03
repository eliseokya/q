#!/bin/bash
# Stop the detection system gracefully

set -e

echo "Stopping atomic-mesh-detection..."

# Stop pipelines first
echo "Stopping detection pipelines..."
if [ -f .pids/detection.pids ]; then
  while read pid; do
    kill -TERM $pid 2>/dev/null || true
  done < .pids/detection.pids
fi

# Wait for graceful shutdown
sleep 5

# Stop nodes
echo "Stopping nodes..."
for chain in ethereum arbitrum polygon base optimism; do
  node-manager stop --chain=$chain --graceful
done

# Clean up
rm -f .pids/detection.pids

echo "Detection system stopped"
