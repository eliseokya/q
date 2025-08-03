#!/bin/bash
# Liquidation hunting pipeline

# Monitor and execute liquidations
lending-rate-extractor --all-protocols | \
liquidation-finder --health-factor<1.05 | \
flash-liquidator --calculate-profit | \
mev-impact-analyzer --liquidation | \
gas-optimizer --competitive | \
bundle-formatter --flashbots | \
execution-feeder --mev-protect

echo "Liquidation hunting pipeline running..."
