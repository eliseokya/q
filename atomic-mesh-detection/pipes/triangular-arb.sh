#!/bin/bash
# Multi-hop triangular arbitrage

# Detect triangular and higher-order arbitrage cycles
event-reader --events=Swap --all-chains | \
price-extractor | \
cycle-detector --min-hops=3 --max-hops=6 | \
triangular-plus --optimize | \
liquidity-filter --check-all-hops | \
gas-cost-calculator --per-hop | \
profit-calculator | \
execution-window-filter --max=3s | \
execution-feeder

echo "Triangular arbitrage pipeline running..."
