#!/bin/bash
# Test detection pipeline

set -e

echo "Testing detection pipeline..."

# Generate test data
./generate-test-data.sh > /tmp/test-input.json

# Run through pipeline
cat /tmp/test-input.json | \
  price-extractor | \
  price-delta-finder --min-delta=0.1% | \
  profit-calculator | \
  tee /tmp/test-output.json

# Verify results
if [ $(jq '.opportunities | length' /tmp/test-output.json) -gt 0 ]; then
  echo "✓ Pipeline test passed"
else
  echo "✗ Pipeline test failed"
  exit 1
fi
