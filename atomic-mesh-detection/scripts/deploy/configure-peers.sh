#!/bin/bash
# Configure peer connections for optimal performance

set -e

echo "Configuring peer networks..."

# Add priority peers for each chain
# Ethereum
unified-reth admin add-peer \
  --chain=ethereum \
  --enode="enode://..." \
  --priority=high

# Configure peer limits
for chain in ethereum arbitrum polygon base optimism; do
  unified-reth admin set-peer-limit \
    --chain=$chain \
    --max-peers=50 \
    --max-priority=10
done

echo "Peer configuration complete"
