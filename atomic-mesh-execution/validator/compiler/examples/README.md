# Compiler Examples

This directory contains example inputs and expected outputs for the Atomic Mesh VM Compiler.

## Running Examples

```bash
# Run a specific example
../pipeline.sh < input/flash-loan.json > output/my-flash-loan-bundle.json

# Compare with expected output
diff output/my-flash-loan-bundle.json output/flash-loan-bundle.json
```

## Example Types

### 1. Flash Loan (flash-loan.json)
Simple flash loan with borrow → swap → swap → repay sequence.

### 2. Parallel Arbitrage (parallel-arb.json)
Cross-chain arbitrage with parallel swaps on different chains.

### 3. Complex Multi-Hop (complex-multi.json)
Multi-chain, multi-protocol operation with various constraints.

## Input Format

All inputs follow the opportunity JSON format:
```json
{
  "opportunity_id": "unique_id",
  "source_chain": "polygon",
  "path": [
    // Array of actions
  ],
  "constraints": {
    // Optional constraints
  }
}
```

## Output Format

All outputs are DSL Bundle JSON:
```json
{
  "type": "Bundle",
  "name": "opportunity_id",
  "startChain": "chain",
  "expr": {
    // Expression tree
  },
  "constraints": [
    // Typed constraints
  ]
}
```