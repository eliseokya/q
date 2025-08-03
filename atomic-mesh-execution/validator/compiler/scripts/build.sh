#!/bin/bash
# Build script for the compiler components

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

echo "Building Atomic Mesh VM Compiler..."
echo "================================="

# Build all components in release mode
cd "$PROJECT_ROOT"
cargo build --release

# Create bin directory
mkdir -p "$PROJECT_ROOT/bin"

# Copy executables to bin directory
echo "Copying executables to bin directory..."
cp target/release/parse-and-validate "$PROJECT_ROOT/bin/"
cp target/release/transform-actions "$PROJECT_ROOT/bin/"
cp target/release/build-expression "$PROJECT_ROOT/bin/"
cp target/release/assemble-bundle "$PROJECT_ROOT/bin/"

# Make pipeline script executable
chmod +x "$PROJECT_ROOT/pipeline.sh"

echo ""
echo "Build complete! Executables are in: $PROJECT_ROOT/bin/"
echo ""
echo "To run the compiler pipeline:"
echo "  ./pipeline.sh < opportunity.json"
echo ""
echo "To test individual components:"
echo "  echo '{...}' | ./bin/parse-and-validate"