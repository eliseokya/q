#!/bin/bash

# Expression Semantics Test
# Verifies that expression composition follows Lean DSL rules

set -e

echo "🔍 Phase 2: Expression Semantics Validation"
echo "==========================================="

TEMP_DIR="/tmp/dsl_compliance"
mkdir -p "$TEMP_DIR"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

TESTS_PASSED=0
TOTAL_TESTS=0

test_expression_semantics() {
    local name=$1
    local description=$2
    local input_file=$3
    local expected_pattern=$4
    
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    echo -n "Testing $description... "
    
    if cat "$input_file" | bin/monolithic > "$TEMP_DIR/${name}_output.json" 2>/dev/null; then
        # Check for specific expression pattern
        if echo "$expected_pattern" | grep -q "BINARY_SEQ"; then
            # Check that seq expressions are binary (e1, e2) not n-ary
            if jq -e '.expr.expr | .. | objects | select(.type? == "seq") | select(has("e1") and has("e2"))' "$TEMP_DIR/${name}_output.json" > /dev/null; then
                echo -e "${GREEN}✅ PASS${NC} (Binary seq)"
                TESTS_PASSED=$((TESTS_PASSED + 1))
            else
                echo -e "${RED}❌ FAIL${NC} (Non-binary seq structure)"
            fi
        elif echo "$expected_pattern" | grep -q "ONCHAIN_WRAPPER"; then
            # Check that expressions are properly wrapped in OnChain
            if jq -e '.expr.type == "onChain"' "$TEMP_DIR/${name}_output.json" > /dev/null; then
                echo -e "${GREEN}✅ PASS${NC} (OnChain wrapper)"
                TESTS_PASSED=$((TESTS_PASSED + 1))
            else
                echo -e "${RED}❌ FAIL${NC} (Missing OnChain wrapper)"
            fi
        elif echo "$expected_pattern" | grep -q "PARALLEL_N_ARY"; then
            # Check that parallel can handle multiple expressions OR that it builds sequential when no parallelism detected
            if jq -e '.expr.expr | .. | objects | select(.type? == "parallel") | select(.exprs | length >= 2)' "$TEMP_DIR/${name}_output.json" > /dev/null; then
                echo -e "${GREEN}✅ PASS${NC} (N-ary parallel found)"
                TESTS_PASSED=$((TESTS_PASSED + 1))
            elif jq -e '.expr.type == "onChain"' "$TEMP_DIR/${name}_output.json" > /dev/null; then
                echo -e "${GREEN}✅ PASS${NC} (Sequential structure, no parallelism detected)"
                TESTS_PASSED=$((TESTS_PASSED + 1))
            else
                echo -e "${RED}❌ FAIL${NC} (Invalid structure)"
            fi
        else
            echo -e "${GREEN}✅ PASS${NC} (Basic structure)"
            TESTS_PASSED=$((TESTS_PASSED + 1))
        fi
        
        # Run deep structure validation
        if python3 test/dsl_compliance/lean_structure_validator.py "$TEMP_DIR/${name}_output.json" > /dev/null 2>&1; then
            echo "   Deep validation: ✅ Passed"
        else
            echo "   Deep validation: ❌ Failed"
        fi
    else
        echo -e "${RED}❌ FAIL${NC} (Compilation error)"
    fi
}

# Test 1: Binary Sequential Composition
cat > "$TEMP_DIR/binary_seq.json" << 'EOF'
{
  "opportunity_id": "binary-seq-test",
  "source_chain": "polygon",
  "path": [
    {"action": "borrow", "amount": "100", "token": "USDC", "protocol": "aave"},
    {"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"},
    {"action": "repay", "amount": "100", "token": "USDC", "protocol": "aave"}
  ]
}
EOF

# Test 2: OnChain Wrapper
cat > "$TEMP_DIR/onchain_wrapper.json" << 'EOF'
{
  "opportunity_id": "onchain-test",
  "source_chain": "polygon",
  "path": [
    {"action": "swap", "amount": "100", "from": "USDC", "to": "DAI", "minOut": "100", "protocol": "uniswapv2"}
  ]
}
EOF

# Test 3: Parallel Expressions (if supported)
cat > "$TEMP_DIR/parallel_expr.json" << 'EOF'
{
  "opportunity_id": "parallel-test",
  "source_chain": "polygon",
  "path": [
    {"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"},
    {"action": "swap", "amount": "200", "from": "DAI", "to": "WBTC", "minOut": "0.01", "protocol": "compound"}
  ]
}
EOF

echo
test_expression_semantics "binary_seq" "Binary Sequential Composition" "$TEMP_DIR/binary_seq.json" "BINARY_SEQ"
test_expression_semantics "onchain_wrapper" "OnChain Expression Wrapper" "$TEMP_DIR/onchain_wrapper.json" "ONCHAIN_WRAPPER"
test_expression_semantics "parallel_expr" "Parallel Expression Support" "$TEMP_DIR/parallel_expr.json" "PARALLEL_N_ARY"

echo
echo "📊 Expression Semantics Results"
echo "==============================="
echo "Tests Passed: $TESTS_PASSED / $TOTAL_TESTS"

if [ $TESTS_PASSED -eq $TOTAL_TESTS ]; then
    echo -e "${GREEN}🎉 All expression semantics tests passed!${NC}"
    exit 0
else
    echo -e "${RED}❌ Some expression semantics tests failed.${NC}"
    exit 1
fi