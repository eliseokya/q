#!/bin/bash
# Validate detection-execution integration

set -e

echo "Validating integration..."

# Check protocol mappings
echo "Checking protocol mappings..."
protocol-mapper --validate-all

# Check bridge compatibility
echo "Checking bridge compatibility..."
bridge-compatibility --check-all

# Check gas coordination
echo "Checking gas coordination..."
gas-coordinator --validate

# Check capability alignment
echo "Checking capabilities..."
capability-checker --compare

# Run end-to-end test
echo "Running end-to-end test..."
./test-with-execution.sh

echo "Integration validation complete!"
