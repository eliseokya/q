# Pipeline Examples

## Simple Arbitrage
```bash
mempool-reader | price-extractor | price-delta-finder | profit-calculator | execution-feeder
```

## Cross-Chain with Validation
```bash
state-reader --all-chains | \
  bridge-opportunity-finder | \
  bridge-readiness-validator | \
  gas-profitability-validator | \
  execution-feeder
```

## Flash Loan Enhanced
```bash
price-scanner | \
  cycle-detector | \
  flash-loan-enhancer | \
  simulation-validator | \
  execution-feeder
```

## Creating Custom Pipelines
Use Unix pipes to combine tools for specific strategies.
