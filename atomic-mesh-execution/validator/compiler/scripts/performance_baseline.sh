#!/bin/bash

# Phase 4: Performance Baseline Measurement
# Establishes current performance and tracks optimization progress

set -e

echo "🔥 Phase 4: Performance Optimization - Baseline Measurement"
echo "==========================================================="

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Performance targets (microseconds)
TARGET_PARSE=300
TARGET_TRANSFORM=400
TARGET_BUILD=600
TARGET_ASSEMBLE=200
TARGET_MONOLITHIC=1500

echo "🎯 Performance Targets:"
echo "  parse-and-validate: < ${TARGET_PARSE}μs"
echo "  transform-actions:  < ${TARGET_TRANSFORM}μs"
echo "  build-expression:   < ${TARGET_BUILD}μs"
echo "  assemble-bundle:    < ${TARGET_ASSEMBLE}μs"
echo "  monolithic:         < ${TARGET_MONOLITHIC}μs"
echo

# Test inputs
simple_input='{"opportunity_id": "simple", "source_chain": "polygon", "path": [{"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}]}'
flash_loan_input='{"opportunity_id": "flash-loan", "source_chain": "polygon", "path": [{"action": "borrow", "amount": "1000", "token": "USDC", "protocol": "aave"}, {"action": "swap", "amount": "500", "from": "USDC", "to": "WETH", "minOut": "0.25", "protocol": "uniswapv2"}, {"action": "repay", "amount": "1000", "token": "USDC", "protocol": "aave"}]}'

# Ensure binaries are built
echo "📦 Building optimized binaries..."
cargo build --release
echo

measure_component() {
    local component=$1
    local input_name=$2
    local input_data=$3
    local target_us=$4
    
    echo -n "  $component ($input_name)... "
    
    # Warm up
    echo "$input_data" | ./bin/$component > /dev/null 2>&1
    
    # Measure multiple runs
    local total_ns=0
    local runs=10
    
    for i in $(seq 1 $runs); do
        local start=$(date +%s%N)
        echo "$input_data" | ./bin/$component > /dev/null 2>&1
        local end=$(date +%s%N)
        local duration_ns=$((end - start))
        total_ns=$((total_ns + duration_ns))
    done
    
    local avg_ns=$((total_ns / runs))
    local avg_us=$((avg_ns / 1000))
    
    if [ $avg_us -le $target_us ]; then
        echo -e "${GREEN}${avg_us}μs ✅${NC} (target: ${target_us}μs)"
        return 0
    else
        local slowdown=$(echo "scale=1; $avg_us / $target_us" | bc -l)
        echo -e "${RED}${avg_us}μs ❌${NC} (${slowdown}x slower than ${target_us}μs target)"
        return 1
    fi
}

measure_monolithic() {
    local input_name=$1
    local input_data=$2
    
    echo -n "  monolithic ($input_name)... "
    
    # Warm up
    echo "$input_data" | ./bin/monolithic > /dev/null 2>&1
    
    # Measure multiple runs
    local total_ns=0
    local runs=10
    
    for i in $(seq 1 $runs); do
        local start=$(date +%s%N)
        echo "$input_data" | ./bin/monolithic > /dev/null 2>&1
        local end=$(date +%s%N)
        local duration_ns=$((end - start))
        total_ns=$((total_ns + duration_ns))
    done
    
    local avg_ns=$((total_ns / runs))
    local avg_us=$((avg_ns / 1000))
    
    if [ $avg_us -le $TARGET_MONOLITHIC ]; then
        echo -e "${GREEN}${avg_us}μs ✅${NC} (target: ${TARGET_MONOLITHIC}μs)"
        return 0
    else
        local slowdown=$(echo "scale=1; $avg_us / $TARGET_MONOLITHIC" | bc -l)
        echo -e "${RED}${avg_us}μs ❌${NC} (${slowdown}x slower than ${TARGET_MONOLITHIC}μs target)"
        return 1
    fi
}

# Component Performance Baseline
echo -e "${BLUE}📊 Individual Component Performance${NC}"
echo "=================================="

components=("parse-and-validate" "transform-actions" "build-expression" "assemble-bundle")
targets=($TARGET_PARSE $TARGET_TRANSFORM $TARGET_BUILD $TARGET_ASSEMBLE)

total_passed=0
total_tests=0

# Test with simple input
echo "Testing with simple input:"
for i in $(seq 0 $((${#components[@]} - 1))); do
    component="${components[$i]}"
    target="${targets[$i]}"
    
    if measure_component "$component" "simple" "$simple_input" "$target"; then
        total_passed=$((total_passed + 1))
    fi
    total_tests=$((total_tests + 1))
done
echo

# Test with flash loan input  
echo "Testing with flash_loan input:"
for i in $(seq 0 $((${#components[@]} - 1))); do
    component="${components[$i]}"
    target="${targets[$i]}"
    
    if measure_component "$component" "flash_loan" "$flash_loan_input" "$target"; then
        total_passed=$((total_passed + 1))
    fi
    total_tests=$((total_tests + 1))
done
echo

# Monolithic Performance Baseline  
echo -e "${BLUE}🚀 Monolithic Pipeline Performance${NC}"
echo "=================================="

if measure_monolithic "simple" "$simple_input"; then
    total_passed=$((total_passed + 1))
fi
total_tests=$((total_tests + 1))

if measure_monolithic "flash_loan" "$flash_loan_input"; then
    total_passed=$((total_passed + 1))
fi
total_tests=$((total_tests + 1))

echo
echo -e "${BLUE}📈 Performance Summary${NC}"
echo "====================="
echo "Performance targets met: $total_passed / $total_tests"

if [ $total_passed -eq $total_tests ]; then
    echo -e "${GREEN}🎉 All performance targets achieved!${NC}"
    echo -e "${GREEN}✅ Phase 4 optimization goals met${NC}"
else
    echo -e "${YELLOW}⚠️  Performance optimization needed${NC}"
    echo -e "${YELLOW}📈 Current optimization opportunity: $((total_tests - total_passed)) components to optimize${NC}"
fi

# Calculate overall speedup needed using simple measurement
echo -n "Measuring current performance... "
start_ns=$(date +%s%N)
echo "$simple_input" | ./bin/monolithic > /dev/null 2>&1
end_ns=$(date +%s%N)
current_us=$(( (end_ns - start_ns) / 1000 ))
speedup_needed=$(echo "scale=1; $current_us / $TARGET_MONOLITHIC" | bc -l)

echo
echo -e "${BLUE}🎯 Optimization Targets${NC}"
echo "======================"
echo "Current performance: ${current_us}μs"
echo "Target performance:  ${TARGET_MONOLITHIC}μs"
echo "Speedup needed:      ${speedup_needed}x"

if (( $(echo "$speedup_needed > 1" | bc -l) )); then
    echo -e "${YELLOW}📊 Phase 4 optimization plan:${NC}"
    echo "  1. JSON parsing optimization (20-30% improvement)"
    echo "  2. Memory allocation reduction (15-25% improvement)"  
    echo "  3. String operations optimization (10-20% improvement)"
    echo "  4. Data structure improvements (10-15% improvement)"
    echo "  5. SIMD optimizations (5-10% improvement)"
    
    echo -e "\n${BLUE}🛠️  Next steps:${NC}"
    echo "  Run: cargo bench --package performance-bench"
    echo "  Run: ./scripts/memory_profiling.sh"
    echo "  Run: ./scripts/cpu_profiling.sh"
fi