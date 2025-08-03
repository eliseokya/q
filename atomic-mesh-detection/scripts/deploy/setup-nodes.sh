#!/bin/bash
# Setup unified nodes for all chains

set -e

echo "Setting up unified nodes..."

# Create data directories
for chain in ethereum arbitrum polygon base optimism; do
  mkdir -p /data/$chain
  echo "Created data directory for $chain"
done

# Initialize databases
./init-databases.sh

# Configure networking
./configure-peers.sh

# Start nodes
for chain in ethereum arbitrum polygon base optimism; do
  echo "Starting $chain node..."
  ./nodes/unified-reth/target/release/unified-reth \
    --chain=$chain \
    --datadir=/data/$chain \
    --config=configs/chains/$chain.toml \
    > logs/$chain.log 2>&1 &
done

echo "All nodes started successfully"
