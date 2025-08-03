#!/bin/bash
# Script to verify that all files are in place for building

set -euo pipefail

echo "Verifying Atomic Mesh VM Compiler Build Readiness..."
echo "=================================================="

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Check for required files
echo "Checking workspace structure..."

# Check main Cargo.toml
if [ ! -f "Cargo.toml" ]; then
    echo "❌ Missing workspace Cargo.toml"
    exit 1
fi
echo "✅ Workspace Cargo.toml found"

# Check for all component directories and files
COMPONENTS=(
    "common"
    "parse-and-validate"
    "transform-actions"
    "build-expression"
    "assemble-bundle"
)

for component in "${COMPONENTS[@]}"; do
    echo ""
    echo "Checking $component..."
    
    # Check directory exists
    if [ ! -d "src/$component" ]; then
        echo "❌ Missing directory: src/$component"
        exit 1
    fi
    
    # Check Cargo.toml
    if [ ! -f "src/$component/Cargo.toml" ]; then
        echo "❌ Missing: src/$component/Cargo.toml"
        exit 1
    fi
    echo "✅ src/$component/Cargo.toml found"
    
    # Check main.rs for binary components
    if [ "$component" != "common" ]; then
        if [ ! -f "src/$component/main.rs" ]; then
            echo "❌ Missing: src/$component/main.rs"
            exit 1
        fi
        echo "✅ src/$component/main.rs found"
    else
        # For common, check mod.rs
        if [ ! -f "src/$component/mod.rs" ]; then
            echo "❌ Missing: src/$component/mod.rs"
            exit 1
        fi
        echo "✅ src/$component/mod.rs found"
    fi
done

# Check for pipeline script
echo ""
echo "Checking pipeline script..."
if [ ! -f "pipeline.sh" ]; then
    echo "❌ Missing pipeline.sh"
    exit 1
fi
echo "✅ pipeline.sh found"

# Check for build and test scripts
echo ""
echo "Checking build scripts..."
if [ ! -f "scripts/build.sh" ]; then
    echo "❌ Missing scripts/build.sh"
    exit 1
fi
echo "✅ scripts/build.sh found"

if [ ! -f "scripts/test.sh" ]; then
    echo "❌ Missing scripts/test.sh"
    exit 1
fi
echo "✅ scripts/test.sh found"

# Check for Makefile
echo ""
echo "Checking Makefile..."
if [ ! -f "Makefile" ]; then
    echo "❌ Missing Makefile"
    exit 1
fi
echo "✅ Makefile found"

# Count Rust source files
echo ""
echo "Counting source files..."
RUST_FILES=$(find src -name "*.rs" -type f | wc -l)
echo "✅ Found $RUST_FILES Rust source files"

# Check test fixtures
echo ""
echo "Checking test fixtures..."
if [ -d "test/fixtures" ]; then
    FIXTURES=$(find test/fixtures -name "*.json" -type f | wc -l)
    echo "✅ Found $FIXTURES test fixture files"
else
    echo "⚠️  No test fixtures directory found"
fi

echo ""
echo "=================================================="
echo "Build Readiness Check: PASSED ✅"
echo ""
echo "All required files are in place!"
echo ""
echo "To build the project, you need Rust installed, then run:"
echo "  cargo build --all"
echo ""
echo "Or use the build script:"
echo "  ./scripts/build.sh"
echo ""