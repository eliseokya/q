#!/bin/bash
# Test with execution system

set -e

echo "Testing with execution system..."

# Start test execution system if needed
if ! nc -z localhost 8888; then
  echo "Starting test execution system..."
  cd ../atomic-mesh-execution
  ./scripts/development/run-test-execution.sh &
  cd -
  sleep 10
fi

# Run test opportunities
./generate-test-opportunities.sh | \
  execution-capability-validator | \
  bundle-formatter | \
  execution-feeder --test

# Check results
sleep 5
if feedback-receiver --check-test; then
  echo "✓ Execution test passed"
else
  echo "✗ Execution test failed"
  exit 1
fi
