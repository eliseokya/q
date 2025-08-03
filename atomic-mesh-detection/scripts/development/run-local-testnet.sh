#!/bin/bash
# Run local testnet for development

set -e

echo "Starting local testnet..."

# Start local chains
for i in {1..5}; do
  port=$((8544 + $i))
  unified-reth testnet \
    --chain-id=$i \
    --port=$port \
    --datadir=/tmp/testnet-$i \
    > logs/testnet-$i.log 2>&1 &
done

# Deploy test contracts
sleep 10
for i in {1..5}; do
  ./deploy-test-contracts.sh --chain-id=$i
done

# Start detection in test mode
TEST_MODE=true ./start-detection.sh

echo "Local testnet running"
echo "Chain 1: http://localhost:8545"
echo "Chain 2: http://localhost:8546"
echo "..."
