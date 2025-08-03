#!/bin/bash
# Rolling update of nodes

set -e

echo "Starting rolling node update..."

for chain in ethereum arbitrum polygon base optimism; do
  echo "Updating $chain node..."
  
  # Stop node
  node-manager stop --chain=$chain --graceful
  
  # Backup state
  unified-reth db backup --chain=$chain --quick
  
  # Update binary
  cp nodes/unified-reth/target/release/unified-reth \
     /usr/local/bin/unified-reth-$chain
  
  # Start node
  node-manager start --chain=$chain
  
  # Wait for sync
  while ! chain-sync-monitor --chain=$chain --check; do
    sleep 10
  done
  
  echo "$chain node updated successfully"
done

echo "Rolling update complete"
