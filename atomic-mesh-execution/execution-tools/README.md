# Module 2: Execution Tools

## Overview

This module contains Unix-style tools for optimizing and orchestrating validated bundles from the DSL compilation layer. Each tool follows the Unix philosophy: do one thing well.

## Architecture

```
Validated Bundle → Bundle Composer → Gas Optimizer → Profitability Checker
                                           ↓
                  Bundle Executor ← Bridge Selector ← Execution Simulator
```

## Tools

### bundle-composer
- Formats validated bundles for execution
- Adds necessary metadata and routing information
- Input: Validated bundle JSON
- Output: Execution-ready bundle JSON

### gas-optimizer
- Applies categorical optimizations to minimize gas costs
- Uses colimit-based path optimization
- Implements monoidal batching for parallel operations
- Achieves 51% gas reduction through mathematical optimization

### profitability-checker
- Validates economic viability after gas optimization
- Checks against current market conditions
- Rejects unprofitable bundles with feedback

### bridge-selector
- Chooses optimal bridge based on:
  - Speed requirements
  - Cost efficiency
  - Liquidity availability
  - Current congestion

### execution-simulator
- Simulates bundle execution before submission
- Validates state changes
- Checks for potential reverts
- Estimates final profitability

### bundle-executor
- Submits optimized bundles to blockchain
- Manages nonces and gas prices
- Handles transaction monitoring
- Reports execution results

### state-monitor
- Monitors blockchain state
- Tracks mempool activity
- Provides real-time updates to other tools

## Usage

### Main Pipeline
```bash
./pipeline/execute-tools < validated-bundle.json > optimized-bundle.json
```

### Individual Tools
```bash
# Compose bundle
./bundle-composer/bin/bundle-composer < validated-bundle.json | \
# Optimize gas
./gas-optimizer/bin/gas-optimizer | \
# Check profitability
./profitability-checker/bin/profitability-checker | \
# Select bridge
./bridge-selector/bin/bridge-selector | \
# Simulate execution
./execution-simulator/bin/execution-simulator | \
# Execute bundle
./bundle-executor/bin/bundle-executor
```

## Configuration

- `config/gas-config.json` - Gas price settings
- `config/profitability-thresholds.json` - Minimum profit requirements
- `config/chain-configs.json` - Chain-specific parameters

## Feedback System

Each tool can send feedback to the detection system:
- `gas-too-high.sh` - When optimization can't achieve profitable gas costs
- `unprofitable.sh` - When bundle isn't economically viable
- `simulation-failed.sh` - When simulation predicts execution failure

## Performance Targets

- Bundle composition: < 5ms
- Gas optimization: < 20ms
- Profitability check: < 10ms
- Bridge selection: < 5ms
- Simulation: < 50ms
- Total pipeline: < 100ms