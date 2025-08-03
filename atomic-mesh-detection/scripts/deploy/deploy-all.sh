#!/bin/bash
# Complete deployment script

set -e

echo "Starting full atomic-mesh-detection deployment..."

# Check requirements
./check-requirements.sh

# Setup nodes
./setup-nodes.sh

# Wait for initial sync
echo "Waiting for initial sync..."
sleep 60

# Verify node health
../operations/health-check.sh

# Start detection components
../operations/start-detection.sh

# Run integration tests
../development/integration-test.sh

echo "Deployment complete!"
echo "Detection system is running"
