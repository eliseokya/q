# Internal API Documentation

## Node Tools API

### mempool-reader
- Output: JSON stream of pending transactions
- Filters: --chain, --min-value, --filter

### state-reader  
- Output: JSON stream of state changes
- Filters: --chain, --contracts, --slots

## Extractor API

### price-extractor
- Input: Events or state
- Output: Normalized prices
- Options: --normalize=usd

## Analyzer API

### price-delta-finder
- Input: Normalized prices
- Output: Arbitrage opportunities
- Options: --min-delta=0.1%

## Integration API

### execution-feeder
- Input: Validated opportunities
- Output: Execution bundles
- Protocol: Unix socket
