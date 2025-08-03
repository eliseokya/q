# Protocol Support

## DEX Protocols

### Uniswap V2
- Chains: All 5
- Features: Swaps, liquidity

### Uniswap V3
- Chains: All 5
- Features: Swaps, concentrated liquidity, flash loans

### Curve
- Chains: Ethereum, Arbitrum, Polygon
- Features: Stable swaps, metapools

### Balancer
- Chains: Ethereum, Arbitrum, Polygon  
- Features: Weighted pools, flash loans

## Lending Protocols

### Aave V3
- Chains: All 5
- Features: Flash loans, supply/borrow

### Compound V3
- Chains: Ethereum, Arbitrum, Polygon, Base
- Features: Flash loans, supply/borrow

## Bridges

### Atomic Mesh Bridge
- Speed: 400ms
- Chains: All pairs

### deBridge
- Speed: 2-5 minutes
- Chains: All pairs

## Adding New Protocols
1. Add to configs/protocol-mappings.toml
2. Ensure execution system support
3. Test with simulation
