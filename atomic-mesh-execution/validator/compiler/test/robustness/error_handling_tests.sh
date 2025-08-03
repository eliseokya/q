#!/bin/bash

# Phase 5: Comprehensive Error Handling Tests
# Tests all error conditions with quality assessment

set -e

echo "🛡️ Phase 5: Robustness - Error Handling Tests"
echo "=============================================="

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

TOTAL_TESTS=0
PASSED_TESTS=0

test_error_case() {
    local name=$1
    local input=$2
    local expected_component=$3
    local expected_code=$4
    local description=$5
    
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    echo -n "  $description... "
    
    # Run test and capture error
    echo "$input" | bin/monolithic > /dev/null 2> /tmp/error_test.json
    local exit_code=$?
    
    if [ $exit_code -ne 0 ]; then
        # Validate error structure
        if jq -e '.error and .component and .code and .message' /tmp/error_test.json > /dev/null 2>&1; then
            local actual_component=$(jq -r '.component' /tmp/error_test.json)
            local actual_code=$(jq -r '.code' /tmp/error_test.json)
            local message=$(jq -r '.message' /tmp/error_test.json)
            
            # Check component and code match expectations
            if [ "$actual_component" = "$expected_component" ] && [ "$actual_code" = "$expected_code" ]; then
                echo -e "${GREEN}✅ PASS${NC}"
                echo "     Component: $actual_component"
                echo "     Code: $actual_code"
                echo "     Message: $message"
                PASSED_TESTS=$((PASSED_TESTS + 1))
            else
                echo -e "${RED}❌ FAIL${NC} (Wrong error: $actual_component/$actual_code, expected: $expected_component/$expected_code)"
            fi
        else
            echo -e "${RED}❌ FAIL${NC} (Invalid error format)"
            echo "     Error output: $(cat /tmp/error_test.json)"
        fi
    else
        echo -e "${RED}❌ FAIL${NC} (Expected error but got success)"
    fi
    echo
}

echo -e "${BLUE}📋 1. JSON Structure Errors${NC}"
echo "=========================="

test_error_case "malformed_json" \
    '{"invalid": json}' \
    "monolithic-parse" \
    "MALFORMED_JSON" \
    "Malformed JSON structure"

test_error_case "missing_opportunity_id" \
    '{"source_chain": "polygon", "path": []}' \
    "monolithic-parse" \
    "MISSING_REQUIRED_FIELD" \
    "Missing opportunity_id field"

test_error_case "missing_path" \
    '{"opportunity_id": "test"}' \
    "monolithic-parse" \
    "MISSING_REQUIRED_FIELD" \
    "Missing path/actions field"

test_error_case "empty_actions" \
    '{"opportunity_id": "test", "source_chain": "polygon", "path": []}' \
    "monolithic-build" \
    "EMPTY_ACTIONS" \
    "Empty actions array"

echo -e "${BLUE}🔧 2. Action Validation Errors${NC}"
echo "=============================="

test_error_case "invalid_action_type" \
    '{"opportunity_id": "test", "source_chain": "polygon", "path": [{"action": "invalid_action", "amount": "100"}]}' \
    "monolithic-transform" \
    "UNKNOWN_ACTION_TYPE" \
    "Unknown action type"

test_error_case "missing_action_field" \
    '{"opportunity_id": "test", "source_chain": "polygon", "path": [{"amount": "100", "token": "USDC"}]}' \
    "monolithic-transform" \
    "MISSING_ACTION_FIELD" \
    "Missing action field"

test_error_case "invalid_amount" \
    '{"opportunity_id": "test", "source_chain": "polygon", "path": [{"action": "swap", "amount": "invalid", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}]}' \
    "monolithic-transform" \
    "INVALID_AMOUNT" \
    "Invalid amount format"

test_error_case "missing_swap_tokens" \
    '{"opportunity_id": "test", "source_chain": "polygon", "path": [{"action": "swap", "amount": "100", "protocol": "uniswapv2"}]}' \
    "monolithic-transform" \
    "MISSING_FIELD" \
    "Missing swap token fields"

echo -e "${BLUE}⛓️ 3. Chain Logic Errors${NC}"
echo "======================="

test_error_case "unknown_chain" \
    '{"opportunity_id": "test", "source_chain": "invalid_chain", "path": [{"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}]}' \
    "monolithic-transform" \
    "UNKNOWN_CHAIN" \
    "Unknown chain"

test_error_case "invalid_bridge_chain" \
    '{"opportunity_id": "test", "source_chain": "polygon", "path": [{"action": "bridge", "to": "invalid_chain", "token": "USDC", "amount": "100"}]}' \
    "monolithic-transform" \
    "UNKNOWN_CHAIN" \
    "Invalid bridge destination"

echo -e "${BLUE}🪙 4. Token/Protocol Errors${NC}"
echo "========================="

test_error_case "unknown_protocol" \
    '{"opportunity_id": "test", "source_chain": "polygon", "path": [{"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "unknown_protocol"}]}' \
    "monolithic-transform" \
    "UNKNOWN_PROTOCOL" \
    "Unknown protocol"

echo -e "${BLUE}📊 5. Constraint Errors${NC}"
echo "===================="

test_error_case "invalid_constraint_deadline" \
    '{"opportunity_id": "test", "source_chain": "polygon", "path": [{"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}], "constraints": {"deadline": "invalid"}}' \
    "monolithic-assemble" \
    "INVALID_CONSTRAINT_VALUE" \
    "Invalid deadline constraint"

test_error_case "invalid_constraint_gas" \
    '{"opportunity_id": "test", "source_chain": "polygon", "path": [{"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}], "constraints": {"max_gas": "not_a_number"}}' \
    "monolithic-assemble" \
    "INVALID_CONSTRAINT_VALUE" \
    "Invalid gas constraint"

echo -e "${BLUE}📈 Error Handling Quality Assessment${NC}"
echo "===================================="

echo "Total Error Tests: $TOTAL_TESTS"
echo -e "Passed: ${GREEN}$PASSED_TESTS${NC}"
echo -e "Failed: ${RED}$((TOTAL_TESTS - PASSED_TESTS))${NC}"

# Error message quality assessment
echo
echo -e "${BLUE}📝 Error Message Quality Check${NC}"
echo "=============================="

# Check if errors include helpful suggestions
echo '{"opportunity_id": "test"}' | bin/monolithic 2> /tmp/quality_test.json 2>/dev/null || true
if jq -e '.suggestion' /tmp/quality_test.json > /dev/null 2>&1; then
    echo "✅ Error suggestions: Present"
    echo "   Example: $(jq -r '.suggestion' /tmp/quality_test.json)"
else
    echo "❌ Error suggestions: Missing"
fi

# Check if errors include context
if jq -e '.context' /tmp/quality_test.json > /dev/null 2>&1; then
    echo "✅ Error context: Present"
else
    echo "⚠️  Error context: Missing (optional)"
fi

# Check timestamp format
if jq -e '.timestamp' /tmp/quality_test.json > /dev/null 2>&1; then
    echo "✅ Error timestamps: Present"
else
    echo "⚠️  Error timestamps: Missing (optional)"
fi

echo
if [ $PASSED_TESTS -eq $TOTAL_TESTS ]; then
    echo -e "${GREEN}🎉 All error handling tests passed!${NC}"
    echo -e "${GREEN}✅ Error handling is production-ready${NC}"
    exit 0
else
    echo -e "${YELLOW}⚠️  Some error handling needs improvement${NC}"
    echo "Failed tests: $((TOTAL_TESTS - PASSED_TESTS))"
    exit 1
fi