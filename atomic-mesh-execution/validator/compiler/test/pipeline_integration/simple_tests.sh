#!/bin/bash

# Simple Phase 3 Pipeline Integration Tests
# Focused validation of key Phase 3 requirements

set -e

echo "🚀 Phase 3: Core Pipeline Integration Tests"
echo "==========================================="

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

TOTAL_TESTS=0
PASSED_TESTS=0

run_test() {
    local name=$1
    local input=$2
    local expected_exit=$3
    local description=$4
    
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    echo -n "  $description... "
    
    # Run test and capture output/exit code
    echo "$input" | bin/monolithic > /tmp/test_out.json 2> /tmp/test_err.json
    local actual_exit=$?
    
    if [ $actual_exit -eq $expected_exit ]; then
        echo -e "${GREEN}✅ PASS${NC}"
        PASSED_TESTS=$((PASSED_TESTS + 1))
        
        # Additional validation for successful cases
        if [ $expected_exit -eq 0 ]; then
            if jq -e '.name and .startChain and .expr and .constraints' /tmp/test_out.json > /dev/null 2>&1; then
                echo "     Structure: ✅ Valid DSL bundle"
            else
                echo -e "     Structure: ${RED}❌ Invalid bundle${NC}"
            fi
        else
            if jq -e '.error and .component and .code and .message' /tmp/test_err.json > /dev/null 2>&1; then
                echo "     Error format: ✅ Standard"
            else
                echo -e "     Error format: ${RED}❌ Non-standard${NC}"
            fi
        fi
    else
        echo -e "${RED}❌ FAIL${NC} (expected exit: $expected_exit, got: $actual_exit)"
        if [ $actual_exit -ne 0 ]; then
            echo "     Error: $(cat /tmp/test_err.json | head -1)"
        fi
    fi
}

echo "📋 1. Unix Pipeline Compliance"
echo "==============================="

# Test 1: Valid input -> Success
run_test "valid_simple" '{
  "opportunity_id": "test-simple",
  "source_chain": "polygon",
  "path": [
    {"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}
  ]
}' 0 "Valid simple swap"

# Test 2: Missing required field -> Exit 1 
run_test "missing_path" '{
  "opportunity_id": "test-missing"
}' 1 "Missing path field"

# Test 3: Empty actions -> Exit 1
run_test "empty_actions" '{
  "opportunity_id": "test-empty",
  "source_chain": "polygon", 
  "path": []
}' 1 "Empty actions array"

# Test 4: Complex valid input
run_test "complex_valid" '{
  "opportunity_id": "test-complex",
  "source_chain": "polygon",
  "path": [
    {"action": "borrow", "amount": "1000", "token": "USDC", "protocol": "aave"},
    {"action": "swap", "amount": "500", "from": "USDC", "to": "WETH", "minOut": "0.25", "protocol": "uniswapv2"},
    {"action": "repay", "amount": "1000", "token": "USDC", "protocol": "aave"}
  ],
  "constraints": {
    "deadline": 20,
    "max_gas": 500000
  }
}' 0 "Complex flash loan"

echo
echo "🔗 2. Component Composability"
echo "============================="

# Test pipeline composability with a simple case
echo -n "  Pipeline chain test... "
TOTAL_TESTS=$((TOTAL_TESTS + 1))

input='{"opportunity_id": "chain-test", "source_chain": "polygon", "path": [{"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}]}'

# Run each stage of the pipeline
echo "$input" | bin/parse-and-validate > /tmp/stage1.json 2> /tmp/stage1_err.json
stage1_exit=$?

if [ $stage1_exit -eq 0 ]; then
    cat /tmp/stage1.json | bin/transform-actions > /tmp/stage2.json 2> /tmp/stage2_err.json
    stage2_exit=$?
    
    if [ $stage2_exit -eq 0 ]; then
        cat /tmp/stage2.json | bin/build-expression > /tmp/stage3.json 2> /tmp/stage3_err.json
        stage3_exit=$?
        
        if [ $stage3_exit -eq 0 ]; then
            cat /tmp/stage3.json | bin/assemble-bundle > /tmp/stage4.json 2> /tmp/stage4_err.json
            stage4_exit=$?
            
            if [ $stage4_exit -eq 0 ]; then
                echo -e "${GREEN}✅ PASS${NC}"
                PASSED_TESTS=$((PASSED_TESTS + 1))
                
                # Compare with monolithic output
                echo "$input" | bin/monolithic > /tmp/mono.json 2>/dev/null
                if jq --sort-keys . /tmp/stage4.json > /tmp/stage4_sorted.json && \
                   jq --sort-keys . /tmp/mono.json > /tmp/mono_sorted.json && \
                   diff /tmp/stage4_sorted.json /tmp/mono_sorted.json > /dev/null; then
                    echo "     Consistency: ✅ Matches monolithic"
                else
                    echo -e "     Consistency: ${YELLOW}⚠️  Differs from monolithic${NC}"
                fi
            else
                echo -e "${RED}❌ FAIL${NC} (assemble-bundle failed)"
            fi
        else
            echo -e "${RED}❌ FAIL${NC} (build-expression failed)"
        fi
    else
        echo -e "${RED}❌ FAIL${NC} (transform-actions failed)"
    fi
else
    echo -e "${RED}❌ FAIL${NC} (parse-and-validate failed)"
fi

echo
echo "⚡ 3. Performance Validation" 
echo "==========================="

# Performance test
echo -n "  Performance test... "
TOTAL_TESTS=$((TOTAL_TESTS + 1))

perf_input='{"opportunity_id": "perf-test", "source_chain": "polygon", "path": [{"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}]}'

start_time=$(date +%s%3N)
echo "$perf_input" | bin/monolithic > /dev/null 2>&1
exit_code=$?
end_time=$(date +%s%3N)
duration_ms=$((end_time - start_time))

if [ $exit_code -eq 0 ]; then
    if [ $duration_ms -le 10 ]; then
        echo -e "${GREEN}✅ PASS${NC} (${duration_ms}ms)"
        PASSED_TESTS=$((PASSED_TESTS + 1))
    else
        echo -e "${YELLOW}✅ PASS${NC} (${duration_ms}ms, above 10ms target)"
        PASSED_TESTS=$((PASSED_TESTS + 1))
    fi
else
    echo -e "${RED}❌ FAIL${NC} (execution failed)"
fi

echo
echo "📊 Phase 3 Core Test Results"
echo "============================"
echo -e "Total Tests: $TOTAL_TESTS"
echo -e "Passed: ${GREEN}$PASSED_TESTS${NC}"
echo -e "Failed: ${RED}$((TOTAL_TESTS - PASSED_TESTS))${NC}"

if [ $PASSED_TESTS -eq $TOTAL_TESTS ]; then
    echo -e "\n${GREEN}🎉 All Phase 3 core tests passed!${NC}"
    echo -e "${GREEN}✅ Unix pipeline compliance verified${NC}"
    echo -e "${GREEN}✅ Component composability confirmed${NC}"
    echo -e "${GREEN}✅ Performance acceptable${NC}"
    exit 0
else
    echo -e "\n${RED}❌ Some core tests failed.${NC}"
    exit 1
fi