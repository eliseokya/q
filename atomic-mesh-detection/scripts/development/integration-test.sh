#!/bin/bash
# Full integration test

set -e

echo "Running integration tests..."

# Test node connectivity
for chain in ethereum arbitrum polygon base optimism; do
  if ! unified-reth rpc --chain=$chain eth_blockNumber > /dev/null; then
    echo "✗ $chain node not responding"
    exit 1
  fi
  echo "✓ $chain node connected"
done

# Test detection components
for component in price-extractor profit-calculator bundle-formatter; do
  if ! echo '{"test": true}' | $component --test > /dev/null; then
    echo "✗ $component test failed"
    exit 1
  fi
  echo "✓ $component test passed"
done

# Test execution integration
if execution-tester --quick; then
  echo "✓ Execution integration test passed"
else
  echo "✗ Execution integration test failed"
  exit 1
fi

echo "All integration tests passed!"
