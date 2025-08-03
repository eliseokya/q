# Practical Compiler Architecture (4 Components)

## Overview
A pragmatic compiler design that balances Unix philosophy with practical performance requirements.

## Component Pipeline

```
                 Opportunity JSON
                        ↓
                 parse-and-validate
                        ↓
                 transform-actions
                        ↓
                 build-expression
                        ↓
                 assemble-bundle
                        ↓
                   DSL Bundle
```

## Component Specifications

### 1. parse-and-validate
**Purpose**: Parse JSON and validate structure, extract all needed data
**Input**: Raw JSON text
**Output**: Validated data structure with all fields
```json
{
  "metadata": {
    "opportunity_id": "opp_123",
    "source_chain": "polygon",
    "target_chain": "arbitrum"
  },
  "actions": [...],
  "constraints": {
    "deadline": 20,
    "max_gas": 1000000
  }
}
```
**Responsibilities**:
- JSON parsing and validation
- Extract metadata
- Extract constraints
- Extract actions array
- Validate all required fields exist

### 2. transform-actions
**Purpose**: Transform all action data into typed, normalized form
**Input**: Validated data from parse-and-validate
**Output**: Transformed data with typed actions
```json
{
  "metadata": {...},
  "actions": [
    {
      "type": "borrow",
      "amount": {"num": 100, "den": 1},
      "token": "WETH",
      "protocol": "Aave",
      "chain": "polygon"
    },
    ...
  ],
  "constraints": [...]
}
```
**Responsibilities**:
- Normalize amounts to rationals
- Map token strings to enums
- Map protocol strings to enums
- Infer chain context from bridges
- Validate chain/protocol compatibility

### 3. build-expression
**Purpose**: Analyze actions and build optimized expression tree
**Input**: Transformed data from transform-actions
**Output**: Data with expression tree
```json
{
  "metadata": {...},
  "expr": {
    "type": "Seq",
    "e1": {"type": "Action", "action": {...}},
    "e2": {
      "type": "Parallel",
      "e1": {...},
      "e2": {...}
    }
  },
  "constraints": [...]
}
```
**Responsibilities**:
- Identify parallel execution opportunities
- Build Expr.seq and Expr.parallel structures
- Add Expr.onChain wrappers
- Optimize expression structure

### 4. assemble-bundle
**Purpose**: Create final DSL Bundle structure
**Input**: Data with expression tree
**Output**: Complete DSL Bundle (in-memory structure)
```
Bundle {
  name: "opp_123",
  startChain: Chain.polygon,
  expr: Expr.seq(...),
  constraints: [Constraint.deadline(20), ...]
}
```
**Responsibilities**:
- Create Bundle structure
- Convert to final DSL types
- Validate completeness
- Ready for analyzer pattern matching

## File Directory Structure

```
atomic-mesh-execution/validator/compiler/
├── src/
│   ├── common/
│   │   ├── types.rs              # All DSL types
│   │   ├── errors.rs             # Error types
│   │   └── rational.rs           # Rational numbers
│   │
│   ├── parse-and-validate/
│   │   ├── main.rs               # Entry point
│   │   ├── parser.rs             # JSON parsing
│   │   ├── validator.rs          # Structure validation
│   │   └── extractor.rs          # Data extraction
│   │
│   ├── transform-actions/
│   │   ├── main.rs               # Entry point
│   │   ├── normalizer.rs         # Amount normalization
│   │   ├── mapper.rs             # Token/protocol mapping
│   │   └── chain_tracker.rs      # Chain inference
│   │
│   ├── build-expression/
│   │   ├── main.rs               # Entry point
│   │   ├── parallel_analyzer.rs  # Parallel detection
│   │   ├── expression_builder.rs # Build Expr tree
│   │   └── optimizer.rs          # Expression optimization
│   │
│   └── assemble-bundle/
│       ├── main.rs               # Entry point
│       └── assembler.rs          # Bundle assembly
│
├── bin/                          # Compiled executables
│   ├── parse-and-validate
│   ├── transform-actions
│   ├── build-expression
│   └── assemble-bundle
│
├── test/
│   ├── fixtures/
│   │   ├── valid/
│   │   │   ├── simple-flash-loan.json
│   │   │   ├── parallel-swaps.json
│   │   │   └── complex-arbitrage.json
│   │   └── invalid/
│   │       ├── malformed.json
│   │       └── missing-fields.json
│   │
│   ├── unit/
│   │   ├── parse_and_validate_test.rs
│   │   ├── transform_actions_test.rs
│   │   ├── build_expression_test.rs
│   │   └── assemble_bundle_test.rs
│   │
│   └── integration/
│       ├── pipeline_test.rs
│       └── optimization_test.rs
│
├── scripts/
│   ├── build.sh                  # Build all components
│   ├── test.sh                   # Run all tests
│   └── run-compiler.sh           # Run full pipeline
│
├── examples/
│   ├── README.md                 # Example documentation
│   ├── input/
│   │   └── flash-loan.json
│   └── output/
│       └── flash-loan-bundle.txt # Text representation
│
├── Cargo.toml                    # Rust workspace
├── Makefile                      # Build automation
├── pipeline.sh                   # Main pipeline script
└── README.md
```

## Pipeline Script

```bash
#!/bin/bash
# compiler/pipeline.sh - Practical 4-component pipeline

set -euo pipefail

BIN_DIR="$(dirname "$0")/bin"

# Run the 4-component pipeline
cat | \
    "$BIN_DIR/parse-and-validate" | \
    "$BIN_DIR/transform-actions" | \
    "$BIN_DIR/build-expression" | \
    "$BIN_DIR/assemble-bundle"

# Exit with status of last command
exit ${PIPESTATUS[-1]}
```

## Implementation Language

**Rust** for all components:
- Excellent JSON handling with serde
- Strong type system matching DSL types
- Fast performance
- Good error handling
- Memory efficient

## Performance Characteristics

| Component | Estimated Time | Memory |
|-----------|---------------|--------|
| parse-and-validate | 0.3ms | 2MB |
| transform-actions | 0.4ms | 3MB |
| build-expression | 0.6ms | 5MB |
| assemble-bundle | 0.2ms | 2MB |
| **Total** | **< 1.5ms** | **~10MB** |

## Key Benefits

1. **Practical**: Only 4 processes vs 12
2. **Maintainable**: Clear component boundaries
3. **Performant**: Less inter-process overhead
4. **Testable**: Each component can still be tested independently
5. **Unix-compliant**: Still follows pipe philosophy

## Testing Strategy

Each component can be tested individually:
```bash
# Test parse-and-validate
cat invalid.json | ./bin/parse-and-validate
# Should output error

# Test transform-actions
cat parsed.json | ./bin/transform-actions
# Should output transformed JSON

# Test full pipeline
cat opportunity.json | ./scripts/run-compiler.sh
# Should output DSL Bundle
```