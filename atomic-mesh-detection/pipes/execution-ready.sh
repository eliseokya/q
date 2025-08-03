#!/bin/bash
# Execution-ready opportunity pipeline

# Full pipeline with all validations
mempool-reader --all-chains | \
tee >(price-extractor) >(liquidity-extractor) >(gas-extractor) | \
price-delta-finder | \
path-builder | \
tee >(state-validator) >(capital-validator) >(bridge-readiness-validator) | \
protocol-mapper | \
gas-coordinator | \
execution-bundle-formatter | \
execution-feeder --validated

echo "Execution-ready pipeline running..."
