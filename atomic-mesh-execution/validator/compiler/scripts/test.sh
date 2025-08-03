#!/bin/bash
# Test script for the compiler components

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

echo "Testing Atomic Mesh VM Compiler..."
echo "================================="

# Run Rust tests
echo "Running unit tests..."
cd "$PROJECT_ROOT"
cargo test --all

echo ""
echo "Running integration tests..."

# Check if binaries exist
if [ ! -d "$PROJECT_ROOT/bin" ]; then
    echo "Binaries not found. Building first..."
    "$SCRIPT_DIR/build.sh"
fi

# Test valid inputs
echo ""
echo "Testing valid inputs..."
for fixture in "$PROJECT_ROOT/test/fixtures/valid"/*.json; do
    if [ -f "$fixture" ]; then
        echo "Testing: $(basename "$fixture")"
        if "$PROJECT_ROOT/pipeline.sh" < "$fixture" > /dev/null 2>&1; then
            echo "  ✓ Success"
        else
            echo "  ✗ Failed (unexpected)"
            exit 1
        fi
    fi
done

# Test invalid inputs
echo ""
echo "Testing invalid inputs..."
for fixture in "$PROJECT_ROOT/test/fixtures/invalid"/*.json; do
    if [ -f "$fixture" ]; then
        echo "Testing: $(basename "$fixture")"
        if "$PROJECT_ROOT/pipeline.sh" < "$fixture" > /dev/null 2>&1; then
            echo "  ✗ Success (unexpected - should have failed)"
            exit 1
        else
            echo "  ✓ Failed as expected"
        fi
    fi
done

echo ""
echo "All tests passed!"