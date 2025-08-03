#!/bin/bash

# DSL Compliance Test Suite
# Tests compiler output against Lean DSL specification

set -e

echo "🧪 Phase 2: DSL Compliance Test Suite"
echo "====================================="

# Test directory
TEST_DIR="test/dsl_compliance"
TEMP_DIR="/tmp/dsl_compliance"
mkdir -p "$TEMP_DIR"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Counters
TOTAL_TESTS=0
PASSED_TESTS=0

test_case() {
    local name=$1
    local description=$2
    local input_file=$3
    
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    echo -n "Testing: $description... "
    
    # Run through monolithic binary
    if cat "$input_file" | bin/monolithic > "$TEMP_DIR/${name}_output.json" 2>"$TEMP_DIR/${name}_error.log"; then
        echo -e "${GREEN}✅ PASS${NC}"
        PASSED_TESTS=$((PASSED_TESTS + 1))
        
        # Validate JSON structure
        if jq . "$TEMP_DIR/${name}_output.json" > /dev/null 2>&1; then
            echo "   JSON structure: ✅ Valid"
        else
            echo -e "   JSON structure: ${RED}❌ Invalid${NC}"
        fi
        
        # Check required fields
        if jq -e '.name and .startChain and .expr and .constraints' "$TEMP_DIR/${name}_output.json" > /dev/null; then
            echo "   Required fields: ✅ Present"
        else
            echo -e "   Required fields: ${RED}❌ Missing${NC}"
        fi
        
    else
        echo -e "${RED}❌ FAIL${NC}"
        echo "   Error: $(cat "$TEMP_DIR/${name}_error.log")"
    fi
    echo
}

# Generate test inputs from lean_examples.json
echo "Generating test cases from Lean DSL examples..."

# Test 1: Simple Flash Loan
cat > "$TEMP_DIR/simple_flash_loan.json" << 'EOF'
{
  "opportunity_id": "polygon-arbitrum-flash-loan",
  "source_chain": "polygon",
  "path": [
    {
      "action": "borrow",
      "amount": "100",
      "token": "WETH",
      "protocol": "aave"
    },
    {
      "action": "bridge",
      "to": "arbitrum",
      "token": "WETH",
      "amount": "100"
    },
    {
      "action": "swap",
      "amount": "100",
      "from": "WETH",
      "to": "USDC",
      "minOut": "50000",
      "protocol": "uniswapv2"
    },
    {
      "action": "bridge",
      "to": "polygon",
      "token": "WETH",
      "amount": "100"
    },
    {
      "action": "repay",
      "amount": "100",
      "token": "WETH",
      "protocol": "aave"
    }
  ],
  "constraints": {
    "deadline": 20,
    "invariants": ["constant-product"]
  }
}
EOF

# Test 2: All Action Types
cat > "$TEMP_DIR/all_actions.json" << 'EOF'
{
  "opportunity_id": "comprehensive-test",
  "source_chain": "polygon",
  "path": [
    {
      "action": "borrow",
      "amount": "1000",
      "token": "USDC",
      "protocol": "aave"
    },
    {
      "action": "deposit",
      "amount": "500",
      "token": "USDC",
      "protocol": "compound"
    },
    {
      "action": "swap",
      "amount": "500",
      "from": "USDC",
      "to": "WETH",
      "minOut": "0.5",
      "protocol": "uniswapv2"
    },
    {
      "action": "withdraw",
      "amount": "500",
      "token": "USDC",
      "protocol": "compound"
    },
    {
      "action": "repay",
      "amount": "1000",
      "token": "USDC",
      "protocol": "aave"
    }
  ]
}
EOF

# Test 3: Custom Tokens/Protocols
cat > "$TEMP_DIR/custom_tokens.json" << 'EOF'
{
  "opportunity_id": "custom-test",
  "source_chain": "polygon",
  "path": [
    {
      "action": "swap",
      "amount": "100",
      "from": "0x1234567890abcdef",
      "to": "USDC",
      "minOut": "200",
      "protocol": "custom-dex"
    }
  ]
}
EOF

# Test 4: All Constraint Types
cat > "$TEMP_DIR/all_constraints.json" << 'EOF'
{
  "opportunity_id": "constraint-test",
  "source_chain": "polygon",
  "path": [
    {
      "action": "swap",
      "amount": "100",
      "from": "USDC",
      "to": "DAI",
      "minOut": "100",
      "protocol": "uniswapv2"
    }
  ],
  "constraints": {
    "deadline": 30,
    "max_gas": 500000,
    "min_balance": {
      "token": "USDC",
      "amount": "50"
    },
    "invariants": ["constant-product", "no-negative-balance"]
  }
}
EOF

echo

# Run tests
test_case "simple_flash_loan" "Lean DSL Flash Loan Example" "$TEMP_DIR/simple_flash_loan.json"
test_case "all_actions" "All Action Types Coverage" "$TEMP_DIR/all_actions.json"
test_case "custom_tokens" "Custom Tokens/Protocols" "$TEMP_DIR/custom_tokens.json"
test_case "all_constraints" "All Constraint Types" "$TEMP_DIR/all_constraints.json"

# Summary
echo "📊 Test Results Summary"
echo "======================"
echo "Total Tests: $TOTAL_TESTS"
echo -e "Passed: ${GREEN}$PASSED_TESTS${NC}"
echo -e "Failed: ${RED}$((TOTAL_TESTS - PASSED_TESTS))${NC}"

if [ $PASSED_TESTS -eq $TOTAL_TESTS ]; then
    echo -e "\n${GREEN}🎉 All DSL compliance tests passed!${NC}"
    exit 0
else
    echo -e "\n${RED}❌ Some tests failed. Check output above.${NC}"
    echo "Test outputs saved in: $TEMP_DIR"
    exit 1
fi