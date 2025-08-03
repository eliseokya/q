#!/bin/bash
# Compiler Pipeline - Transforms opportunity JSON to DSL Bundle
# Uses 4 focused components for optimal balance of modularity and performance

set -euo pipefail

# Define the 4 components
COMPONENTS=(
    "parse-and-validate"
    "transform-actions"
    "build-expression"
    "assemble-bundle"
)

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BIN_DIR="$SCRIPT_DIR/bin"

# Verify all components are available
for component in "${COMPONENTS[@]}"; do
    if [ ! -x "$BIN_DIR/$component" ]; then
        echo "Error: Component $component not found in $BIN_DIR" >&2
        echo "Please build all compiler components first" >&2
        exit 1
    fi
done

# Check if stdin is provided
if [ -t 0 ]; then
    echo "Error: No input provided. Expected opportunity JSON via stdin." >&2
    echo "Usage: ./pipeline.sh < opportunity.json" >&2
    exit 1
fi

# Execute 4-component pipeline
# Each component reads from stdin and writes to stdout
# Errors go to stderr and cause pipeline to fail
#
# Pipeline flow:
# 1. parse-and-validate: Parse JSON, validate structure, extract metadata/actions/constraints
# 2. transform-actions: Convert to typed format (rationals, enums, chain inference)
# 3. build-expression: Build expression tree with parallel optimization
# 4. assemble-bundle: Create final Bundle structure

cat | \
    "$BIN_DIR/parse-and-validate" | \
    "$BIN_DIR/transform-actions" | \
    "$BIN_DIR/build-expression" | \
    "$BIN_DIR/assemble-bundle"

# Exit with status of last component in pipeline
exit ${PIPESTATUS[-1]}