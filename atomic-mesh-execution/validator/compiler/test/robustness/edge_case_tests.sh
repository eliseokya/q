#!/bin/bash

# Phase 5: Edge Case Robustness Tests
# Tests boundary conditions and unusual inputs

set -e

echo "🎯 Phase 5: Edge Case Robustness Tests"
echo "======================================"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

TOTAL_TESTS=0
PASSED_TESTS=0

test_edge_case() {
    local name=$1
    local input=$2
    local should_succeed=$3
    local description=$4
    
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    echo -n "  $description... "
    
    # Run test
    echo "$input" | bin/monolithic > /tmp/edge_test_out.json 2> /tmp/edge_test_err.json
    local exit_code=$?
    
    if [ "$should_succeed" = "true" ]; then
        if [ $exit_code -eq 0 ]; then
            # Validate output structure
            if jq -e '.name and .startChain and .expr and .constraints' /tmp/edge_test_out.json > /dev/null 2>&1; then
                echo -e "${GREEN}✅ PASS${NC}"
                PASSED_TESTS=$((PASSED_TESTS + 1))
            else
                echo -e "${RED}❌ FAIL${NC} (Invalid output structure)"
            fi
        else
            echo -e "${RED}❌ FAIL${NC} (Unexpected failure: $(cat /tmp/edge_test_err.json | head -1))"
        fi
    else
        if [ $exit_code -ne 0 ]; then
            # Should fail - check error format
            if jq -e '.error and .component and .code and .message' /tmp/edge_test_err.json > /dev/null 2>&1; then
                echo -e "${GREEN}✅ PASS${NC} (Failed as expected)"
                PASSED_TESTS=$((PASSED_TESTS + 1))
            else
                echo -e "${RED}❌ FAIL${NC} (Invalid error format)"
            fi
        else
            echo -e "${RED}❌ FAIL${NC} (Should have failed but succeeded)"
        fi
    fi
}

echo -e "${BLUE}📊 1. Numerical Edge Cases${NC}"
echo "=========================="

test_edge_case "zero_amount" \
    '{"opportunity_id": "zero-test", "source_chain": "polygon", "path": [{"action": "swap", "amount": "0", "from": "USDC", "to": "WETH", "minOut": "0", "protocol": "uniswapv2"}]}' \
    "true" \
    "Zero amounts"

test_edge_case "very_large_amount" \
    '{"opportunity_id": "large-test", "source_chain": "polygon", "path": [{"action": "swap", "amount": "999999999999999999", "from": "USDC", "to": "WETH", "minOut": "1", "protocol": "uniswapv2"}]}' \
    "true" \
    "Very large amounts"

test_edge_case "decimal_precision" \
    '{"opportunity_id": "precision-test", "source_chain": "polygon", "path": [{"action": "swap", "amount": "0.000000000000000001", "from": "USDC", "to": "WETH", "minOut": "0.000000000000000001", "protocol": "uniswapv2"}]}' \
    "true" \
    "High decimal precision"

test_edge_case "negative_amount" \
    '{"opportunity_id": "negative-test", "source_chain": "polygon", "path": [{"action": "swap", "amount": "-100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}]}' \
    "false" \
    "Negative amounts (should fail)"

echo -e "${BLUE}📝 2. String Edge Cases${NC}"
echo "===================="

test_edge_case "very_long_id" \
    '{"opportunity_id": "'$(printf 'a%.0s' {1..1000})'", "source_chain": "polygon", "path": [{"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}]}' \
    "true" \
    "Very long opportunity ID"

test_edge_case "unicode_characters" \
    '{"opportunity_id": "test-🚀-émojì", "source_chain": "polygon", "path": [{"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}]}' \
    "true" \
    "Unicode characters in ID"

test_edge_case "special_characters" \
    '{"opportunity_id": "test-!@#$%^&*()_+-=[]{}|;:,.<>?", "source_chain": "polygon", "path": [{"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}]}' \
    "true" \
    "Special characters in ID"

test_edge_case "empty_string_id" \
    '{"opportunity_id": "", "source_chain": "polygon", "path": [{"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}]}' \
    "false" \
    "Empty opportunity ID (should fail)"

echo -e "${BLUE}🔗 3. Chain Transition Edge Cases${NC}"
echo "==============================="

test_edge_case "same_chain_bridge" \
    '{"opportunity_id": "same-chain", "source_chain": "polygon", "path": [{"action": "bridge", "to": "polygon", "token": "USDC", "amount": "100"}]}' \
    "true" \
    "Bridge to same chain"

test_edge_case "multiple_bridges" \
    '{"opportunity_id": "multi-bridge", "source_chain": "polygon", "path": [
        {"action": "bridge", "to": "arbitrum", "token": "USDC", "amount": "100"},
        {"action": "bridge", "to": "polygon", "token": "USDC", "amount": "100"},
        {"action": "bridge", "to": "arbitrum", "token": "USDC", "amount": "100"}
    ]}' \
    "true" \
    "Multiple chain bridges"

echo -e "${BLUE}🪙 4. Token Edge Cases${NC}"
echo "==================="

test_edge_case "custom_token_address" \
    '{"opportunity_id": "custom-token", "source_chain": "polygon", "path": [{"action": "swap", "amount": "100", "from": "0x1234567890abcdef1234567890abcdef12345678", "to": "USDC", "minOut": "100", "protocol": "uniswapv2"}]}' \
    "true" \
    "Custom token with address"

test_edge_case "same_token_swap" \
    '{"opportunity_id": "same-token", "source_chain": "polygon", "path": [{"action": "swap", "amount": "100", "from": "USDC", "to": "USDC", "minOut": "100", "protocol": "uniswapv2"}]}' \
    "true" \
    "Swap same token (USDC -> USDC)"

echo -e "${BLUE}⚖️ 5. Constraint Edge Cases${NC}"
echo "========================="

test_edge_case "zero_deadline" \
    '{"opportunity_id": "zero-deadline", "source_chain": "polygon", "path": [{"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}], "constraints": {"deadline": 0}}' \
    "true" \
    "Zero deadline constraint"

test_edge_case "massive_gas_limit" \
    '{"opportunity_id": "huge-gas", "source_chain": "polygon", "path": [{"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}], "constraints": {"max_gas": 999999999999}}' \
    "true" \
    "Very large gas limit"

test_edge_case "all_constraint_types" \
    '{"opportunity_id": "all-constraints", "source_chain": "polygon", "path": [{"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}], "constraints": {"deadline": 20, "max_gas": 500000, "min_balance": {"token": "USDC", "amount": "50"}, "invariants": ["constant-product", "no-negative-balance"]}}' \
    "true" \
    "All constraint types together"

echo -e "${BLUE}📏 6. Size Edge Cases${NC}"
echo "==================="

# Generate large action sequence
large_actions=""
for i in {1..50}; do
    if [ $i -gt 1 ]; then
        large_actions+=","
    fi
    large_actions+="{\"action\": \"swap\", \"amount\": \"$i\", \"from\": \"USDC\", \"to\": \"WETH\", \"minOut\": \"0.5\", \"protocol\": \"uniswapv2\"}"
done

test_edge_case "large_action_sequence" \
    "{\"opportunity_id\": \"large-sequence\", \"source_chain\": \"polygon\", \"path\": [$large_actions]}" \
    "true" \
    "Large action sequence (50 actions)"

test_edge_case "single_action" \
    '{"opportunity_id": "single", "source_chain": "polygon", "path": [{"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}]}' \
    "true" \
    "Single action (minimal case)"

echo
echo -e "${BLUE}📊 Edge Case Test Summary${NC}"
echo "========================"
echo "Total Edge Case Tests: $TOTAL_TESTS"
echo -e "Passed: ${GREEN}$PASSED_TESTS${NC}"
echo -e "Failed: ${RED}$((TOTAL_TESTS - PASSED_TESTS))${NC}"

if [ $PASSED_TESTS -eq $TOTAL_TESTS ]; then
    echo -e "\n${GREEN}🎉 All edge case tests passed!${NC}"
    echo -e "${GREEN}✅ System handles edge cases robustly${NC}"
    exit 0
else
    echo -e "\n${YELLOW}⚠️  Some edge cases need attention${NC}"
    echo "Failed edge case tests: $((TOTAL_TESTS - PASSED_TESTS))"
    exit 1
fi