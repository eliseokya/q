#!/bin/bash
# Update capability manifest

set -e

echo "Updating capability manifest..."

# Query current capabilities
current_capabilities=$(capability-checker --json)

# Compare with stored
if [ -f configs/execution-capabilities.json ]; then
  diff_capabilities=$(echo $current_capabilities | \
    jq -r '.diff' configs/execution-capabilities.json)
fi

# Update if changed
if [ ! -z "$diff_capabilities" ]; then
  echo "Capabilities changed, updating..."
  echo $current_capabilities > configs/execution-capabilities.json
  
  # Notify components
  capability-updater --notify-all
fi

echo "Capability update complete"
