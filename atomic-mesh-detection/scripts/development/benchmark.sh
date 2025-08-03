#!/bin/bash
# Benchmark detection performance

set -e

echo "Running performance benchmark..."

# Component benchmarks
for component in price-extractor price-delta-finder profit-calculator; do
  echo "Benchmarking $component..."
  time (
    for i in {1..1000}; do
      echo '{"test": "data"}' | $component > /dev/null
    done
  )
done

# Full pipeline benchmark
echo "Benchmarking full pipeline..."
time ./pipes/simple-arb.sh --benchmark --duration=60s

# Generate report
performance-profiler --generate-report > benchmark-report.txt

echo "Benchmark complete: benchmark-report.txt"
