# Final Compiler Architecture

## Overview
The compiler transforms opportunity JSON into DSL Bundle structures that fully leverage the mathematical model's optimization capabilities, including parallel execution.

## Complete Pipeline

```
                    Opportunity JSON
                          ↓
                    validate-json
                          ↓
                    ┌─────┴─────┐
                    ↓           ↓
            extract-metadata   extract-actions
                    ↓           ↓
            extract-constraints normalize-amounts
                    ↓           ↓
                    ↓       map-tokens
                    ↓           ↓
                    ↓       map-protocols
                    ↓           ↓
                    ↓       infer-chains
                    ↓           ↓
                    ↓       identify-parallel-groups
                    ↓           ↓
                    ↓       build-expressions
                    ↓           ↓
                    ↓       wrap-chain-contexts
                    ↓           ↓
                    └─────┬─────┘
                          ↓
                    assemble-bundle
                          ↓
                      DSL Bundle
```

## Component Specifications

### Core Component (Entry Point)
1. **validate-json**
   - Input: Raw text
   - Output: Valid JSON or error
   - Purpose: Ensure well-formed JSON input

### Metadata Pipeline (Left Branch)
2. **extract-metadata**
   - Input: Validated JSON
   - Output: {name: string, source_chain: string, target_chain: string}
   - Purpose: Extract bundle metadata

3. **extract-constraints**
   - Input: Validated JSON
   - Output: Array of constraint objects
   - Purpose: Extract deadline, gas limits, min balances, invariants

### Action Pipeline (Right Branch)
4. **extract-actions**
   - Input: Validated JSON
   - Output: Array of raw action objects
   - Purpose: Extract the path array

5. **normalize-amounts**
   - Input: Raw actions
   - Output: Actions with rational amounts {num: n, den: d}
   - Purpose: Convert string amounts to rationals

6. **map-tokens**
   - Input: Actions with rational amounts
   - Output: Actions with Token enum values
   - Purpose: Map "WETH" → Token.WETH

7. **map-protocols**
   - Input: Actions with mapped tokens
   - Output: Actions with Protocol enum values
   - Purpose: Map "aave" → Protocol.Aave

8. **infer-chains**
   - Input: Actions with protocols
   - Output: Actions with chain context added
   - Purpose: Track chain transitions through bridges

9. **identify-parallel-groups**
   - Input: Chain-annotated actions
   - Output: Array of action groups [{parallel: true/false, actions: [...]}]
   - Purpose: Identify independent actions that can execute in parallel

10. **build-expressions**
    - Input: Grouped actions
    - Output: Expression tree with Expr.seq and Expr.parallel
    - Purpose: Build optimized expression structure

11. **wrap-chain-contexts**
    - Input: Expression tree
    - Output: Expression with Expr.onChain wrappers
    - Purpose: Add chain execution contexts

### Merge Component
12. **assemble-bundle**
    - Input: {metadata: {...}, constraints: [...], expr: ...}
    - Output: Complete DSL Bundle
    - Purpose: Assemble final Bundle structure

## Parallel Optimization Logic

The `identify-parallel-groups` component identifies parallelizable actions based on:
- Different chains (cross-chain operations)
- Different protocols (no shared state)
- No data dependencies (output of one isn't input to another)

Example transformation:
```json
// Sequential actions
[
  {action: "swap", chain: "polygon", protocol: "UniswapV2"},
  {action: "swap", chain: "arbitrum", protocol: "UniswapV2"},
  {action: "repay", chain: "polygon", protocol: "Aave"}
]

// Grouped for parallel execution
[
  {
    parallel: true,
    actions: [
      {action: "swap", chain: "polygon", protocol: "UniswapV2"},
      {action: "swap", chain: "arbitrum", protocol: "UniswapV2"}
    ]
  },
  {
    parallel: false,
    actions: [{action: "repay", chain: "polygon", protocol: "Aave"}]
  }
]
```

## File Directory Structure

```
atomic-mesh-execution/validator/compiler/
├── src/
│   ├── common/
│   │   ├── types.rs              # Shared types matching DSL
│   │   ├── errors.rs             # Common error types
│   │   ├── rational.rs           # Rational number implementation
│   │   └── utils.rs              # Shared utilities
│   │
│   ├── core/
│   │   └── validate-json/
│   │       └── main.rs           # JSON validation
│   │
│   ├── metadata-pipeline/
│   │   ├── extract-metadata/
│   │   │   └── main.rs           # Extract name, chains
│   │   └── extract-constraints/
│   │       └── main.rs           # Extract all constraint types
│   │
│   ├── action-pipeline/
│   │   ├── extract-actions/
│   │   │   └── main.rs           # Extract action array
│   │   ├── normalize-amounts/
│   │   │   └── main.rs           # String → Rational conversion
│   │   ├── map-tokens/
│   │   │   └── main.rs           # String → Token enum
│   │   ├── map-protocols/
│   │   │   └── main.rs           # String → Protocol enum
│   │   ├── infer-chains/
│   │   │   └── main.rs           # Add chain context
│   │   ├── identify-parallel-groups/
│   │   │   └── main.rs           # Parallel optimization analysis
│   │   ├── build-expressions/
│   │   │   └── main.rs           # Build Expr tree with seq/parallel
│   │   └── wrap-chain-contexts/
│   │       └── main.rs           # Add Expr.onChain wrappers
│   │
│   └── merge/
│       └── assemble-bundle/
│           └── main.rs           # Merge pipelines into Bundle
│
├── bin/                          # Compiled executables
│   ├── validate-json
│   ├── extract-metadata
│   ├── extract-constraints
│   ├── extract-actions
│   ├── normalize-amounts
│   ├── map-tokens
│   ├── map-protocols
│   ├── infer-chains
│   ├── identify-parallel-groups
│   ├── build-expressions
│   ├── wrap-chain-contexts
│   └── assemble-bundle
│
├── test/
│   ├── fixtures/
│   │   ├── simple-sequential.json
│   │   ├── parallel-opportunity.json
│   │   ├── complex-constraints.json
│   │   └── invalid-examples/
│   ├── unit/                     # Tests for each component
│   ├── integration/              # Pipeline tests
│   └── optimization/             # Parallel optimization tests
│
├── scripts/
│   ├── build-all.sh             # Build all components
│   ├── run-metadata-pipeline.sh  # Run left branch
│   ├── run-action-pipeline.sh    # Run right branch
│   ├── run-full-compiler.sh      # Run complete compiler
│   └── test-parallel-optimization.sh
│
├── examples/
│   ├── sequential-bundle.json    # Input/output examples
│   ├── parallel-bundle.json
│   └── optimized-bundle.sexp     # Example output
│
├── docs/
│   ├── parallel-optimization.md  # How parallel detection works
│   └── component-specs.md        # Detailed specifications
│
├── Cargo.toml                    # Rust workspace
├── Makefile                      # Build automation
├── pipeline.sh                   # Main execution script
└── README.md
```

## Pipeline Execution Script

```bash
#!/bin/bash
# compiler/pipeline.sh - Complete compiler pipeline with parallel execution

set -euo pipefail

# Run both pipelines in parallel and merge
{
    cat | tee >(
        # Metadata pipeline
        ./bin/extract-metadata > /tmp/metadata.json &&
        ./bin/extract-constraints > /tmp/constraints.json
    ) | (
        # Action pipeline
        ./bin/extract-actions |
        ./bin/normalize-amounts |
        ./bin/map-tokens |
        ./bin/map-protocols |
        ./bin/infer-chains |
        ./bin/identify-parallel-groups |
        ./bin/build-expressions |
        ./bin/wrap-chain-contexts > /tmp/expression.json
    )
} | ./bin/validate-json

# Wait for both pipelines
wait

# Merge results
jq -s '{metadata: .[0], constraints: .[1], expr: .[2]}' \
    /tmp/metadata.json \
    /tmp/constraints.json \
    /tmp/expression.json |
./bin/assemble-bundle
```

## Key Design Decisions

1. **Parallel Optimization Built-in**: The compiler identifies and leverages parallel execution opportunities
2. **Clean Separation**: Metadata and action pipelines run independently
3. **Unix Philosophy**: Each component does one thing well
4. **Type Safety**: Progressive transformation to typed values
5. **Optimization-First**: Structure supports the mathematical model's optimization capabilities

## Performance Targets

- Total pipeline: < 2ms
- Parallel group identification: < 0.3ms
- Maximum memory: 15MB (increased for parallel analysis)
- All components < 0.2ms individually