#!/bin/bash
# Sync detection with execution system

set -e

echo "Syncing with execution system..."

# Get execution capabilities
capability-checker --save > /tmp/exec-capabilities.json

# Update detection configuration
capability-updater --input=/tmp/exec-capabilities.json

# Restart affected components
echo "Restarting components..."
systemctl restart detection-integration

# Verify sync
execution-tester --verify-sync

echo "Sync complete"
