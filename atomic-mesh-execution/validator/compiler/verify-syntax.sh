#!/bin/bash
# Basic syntax verification for Rust files

set -euo pipefail

echo "Performing basic syntax checks on Rust files..."
echo "=============================================="

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Check for basic syntax patterns in Rust files
ERROR_COUNT=0

echo "Checking for unclosed braces and parentheses..."
for file in $(find src -name "*.rs" -type f); do
    # Count opening and closing braces
    OPEN_BRACES=$(grep -o '{' "$file" | wc -l || true)
    CLOSE_BRACES=$(grep -o '}' "$file" | wc -l || true)
    
    if [ "$OPEN_BRACES" -ne "$CLOSE_BRACES" ]; then
        echo "⚠️  Brace mismatch in $file: { = $OPEN_BRACES, } = $CLOSE_BRACES"
        ((ERROR_COUNT++))
    fi
    
    # Count opening and closing parentheses
    OPEN_PARENS=$(grep -o '(' "$file" | wc -l || true)
    CLOSE_PARENS=$(grep -o ')' "$file" | wc -l || true)
    
    if [ "$OPEN_PARENS" -ne "$CLOSE_PARENS" ]; then
        echo "⚠️  Parenthesis mismatch in $file: ( = $OPEN_PARENS, ) = $CLOSE_PARENS"
        ((ERROR_COUNT++))
    fi
done

echo ""
echo "Checking for common import patterns..."
# Check that all files using common types import them
for file in $(find src -name "*.rs" -type f | grep -v "src/common/"); do
    if grep -q "CompilerError\|Token\|Protocol\|Chain\|Action\|Expr\|Rational" "$file"; then
        if ! grep -q "use common::\|use crate::common::" "$file"; then
            echo "⚠️  File $file uses common types but may be missing imports"
            ((ERROR_COUNT++))
        fi
    fi
done

echo ""
echo "Checking module structure..."
# Verify each component has required modules
COMPONENTS=(
    "parse-and-validate:parser,validator,extractor"
    "transform-actions:normalizer,mapper,chain_tracker"
    "build-expression:parallel_analyzer,expression_builder,optimizer"
    "assemble-bundle:assembler"
)

for component_spec in "${COMPONENTS[@]}"; do
    IFS=':' read -r component modules <<< "$component_spec"
    IFS=',' read -ra MODULE_ARRAY <<< "$modules"
    
    for module in "${MODULE_ARRAY[@]}"; do
        if [ ! -f "src/$component/$module.rs" ]; then
            echo "❌ Missing module: src/$component/$module.rs"
            ((ERROR_COUNT++))
        else
            # Check if module is declared in main.rs
            if ! grep -q "mod $module;" "src/$component/main.rs"; then
                echo "⚠️  Module $module not declared in src/$component/main.rs"
                ((ERROR_COUNT++))
            fi
        fi
    done
done

echo ""
echo "Checking for #[cfg(test)] blocks..."
TEST_COUNT=$(grep -r "#\[cfg(test)\]" src --include="*.rs" | wc -l || true)
echo "✅ Found $TEST_COUNT test modules"

echo ""
echo "=============================================="
if [ "$ERROR_COUNT" -eq 0 ]; then
    echo "Syntax Check: PASSED ✅"
    echo ""
    echo "Basic syntax verification complete!"
    echo "No obvious syntax errors detected."
else
    echo "Syntax Check: WARNINGS ⚠️"
    echo ""
    echo "Found $ERROR_COUNT potential issues."
    echo "These may need investigation before building."
fi
echo ""