#!/bin/bash
# Simple arbitrage detection pipeline

# Extract prices, find deltas, calculate profit, and send to execution
mempool-reader --chain=all --filter=dex | \
price-extractor --normalize=usd | \
price-delta-finder --min-delta=0.1% | \
profit-calculator --include-gas | \
profitability-filter --min=50 | \
bundle-formatter | \
execution-feeder

echo "Simple arbitrage pipeline running..."
