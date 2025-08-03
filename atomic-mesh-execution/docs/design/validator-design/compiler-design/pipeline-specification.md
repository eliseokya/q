# Compiler Pipeline Specification

## Overview

The compiler is designed as a Unix-style pipeline of 4 specialized components, each performing a focused set of transformations. This design balances modularity with practical performance requirements.

## Pipeline Architecture

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

**Executable**: `bin/parse-and-validate`

**Input** (stdin): Raw JSON text
```json
{
  "opportunity_id": "opp_123",
  "source_chain": "polygon",
  "path": [
    {"action": "borrow", "amount": "100", "token": "WETH", "protocol": "aave"}
  ],
  "constraints": {"deadline": 20}
}
```

**Output** (stdout): Validated and structured JSON
```json
{
  "metadata": {
    "opportunity_id": "opp_123",
    "source_chain": "polygon"
  },
  "actions": [
    {"action": "borrow", "amount": "100", "token": "WETH", "protocol": "aave"}
  ],
  "constraints": {
    "deadline": 20,
    "max_gas": null
  }
}
```

**Exit Codes**:
- 0: Success
- 1: Malformed JSON
- 2: Missing required fields
- 3: Invalid field types

### 2. transform-actions

**Purpose**: Transform all action data into typed, normalized form

**Executable**: `bin/transform-actions`

**Input** (stdin): Validated data from parse-and-validate

**Output** (stdout): Transformed data with typed actions
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
    }
  ],
  "constraints": {...}
}
```

**Exit Codes**:
- 0: Success
- 1: Unknown token
- 2: Unknown protocol
- 3: Invalid amount
- 4: Chain inference failure

### 3. build-expression

**Purpose**: Analyze actions and build optimized expression tree

**Executable**: `bin/build-expression`

**Input** (stdin): Transformed data from transform-actions

**Output** (stdout): Data with expression tree
```json
{
  "metadata": {...},
  "expr": {
    "type": "Action",
    "action": {
      "type": "borrow",
      "amount": {"num": 100, "den": 1},
      "token": "WETH",
      "protocol": "Aave"
    }
  },
  "constraints": {...}
}
```

**Exit Codes**:
- 0: Success
- 1: Invalid action sequence
- 2: Expression building failure

### 4. assemble-bundle

**Purpose**: Create final DSL Bundle structure

**Executable**: `bin/assemble-bundle`

**Input** (stdin): Data with expression tree from build-expression

**Output** (stdout): Complete DSL Bundle
```json
{
  "type": "Bundle",
  "name": "opp_123",
  "startChain": "polygon",
  "expr": {...},
  "constraints": [
    {"type": "deadline", "blocks": 20}
  ]
}
```

**Exit Codes**:
- 0: Success
- 1: Bundle assembly failure

## Pipeline Execution

### Using the pipeline script
```bash
# Execute full pipeline
./pipeline.sh < opportunity.json > bundle.json

# With error handling
if ./pipeline.sh < opportunity.json > bundle.json 2> error.log; then
    echo "Compilation successful"
else
    echo "Compilation failed, see error.log"
fi
```

### Manual component chaining
```bash
# Step by step execution
cat opportunity.json | ./bin/parse-and-validate > stage1.json
cat stage1.json | ./bin/transform-actions > stage2.json
cat stage2.json | ./bin/build-expression > stage3.json
cat stage3.json | ./bin/assemble-bundle > bundle.json

# Or as a single pipeline
cat opportunity.json | \
  ./bin/parse-and-validate | \
  ./bin/transform-actions | \
  ./bin/build-expression | \
  ./bin/assemble-bundle > bundle.json
```

## Error Format

All components output errors to stderr in this format:
```json
{
  "error": true,
  "component": "transform-actions",
  "code": "UNKNOWN_TOKEN",
  "message": "Unknown token: 'WBTC'",
  "context": {
    "action_index": 2,
    "field": "token",
    "value": "WBTC"
  },
  "suggestion": "Supported tokens: ETH, WETH, USDC, DAI"
}
```

## Performance Requirements

| Component | Target | Budget Allocation |
|-----------|--------|------------------|
| parse-and-validate | < 0.3ms | 20% |
| transform-actions | < 0.4ms | 27% |
| build-expression | < 0.6ms | 40% |
| assemble-bundle | < 0.2ms | 13% |
| **Total** | **< 1.5ms** | **100%** |

## Testing Components

### Individual component testing
```bash
# Test parse-and-validate with invalid JSON
echo '{"invalid": json}' | ./bin/parse-and-validate
# Expected: Error to stderr, exit code 1

# Test transform-actions with unknown token
echo '{"actions": [{"token": "UNKNOWN"}]}' | ./bin/transform-actions
# Expected: Error to stderr, exit code 1

# Test successful compilation
cat test/fixtures/flash_loan.json | ./pipeline.sh
# Expected: Valid bundle to stdout, exit code 0
```

### Performance testing
```bash
# Measure individual component performance
time echo "$INPUT" | ./bin/parse-and-validate > /dev/null

# Measure full pipeline
time ./pipeline.sh < large_opportunity.json > /dev/null
```

## Implementation Requirements

### All Components Must:
1. Read from stdin, write to stdout
2. Output errors to stderr only
3. Return appropriate exit codes
4. Be stateless (no side effects)
5. Handle streaming for large inputs
6. Validate inputs before processing
7. Produce deterministic outputs

### Recommended Implementation:
- **Language**: Rust (for performance and type safety)
- **JSON library**: serde_json
- **Error handling**: anyhow or custom error types
- **Logging**: env_logger (only in debug mode)

## Component Communication Protocol

### Success Flow:
```
stdin → [component] → stdout
         ↓ (exit 0)
```

### Error Flow:
```
stdin → [component] → stderr (error JSON)
         ↓ (exit 1-255)
```

## Debugging Support

### Enable debug logging:
```bash
RUST_LOG=debug ./pipeline.sh < opportunity.json
```

### Inspect intermediate outputs:
```bash
# Save each stage
cat opportunity.json | ./bin/parse-and-validate | tee stage1.json | \
  ./bin/transform-actions | tee stage2.json | \
  ./bin/build-expression | tee stage3.json | \
  ./bin/assemble-bundle > final.json
```

### Component health check:
```bash
# Each component should support --version
./bin/parse-and-validate --version
# Output: parse-and-validate 0.1.0
```

## Future Extensions

### Parallel Processing
For batch operations, components can process multiple inputs:
```bash
# Process multiple opportunities in parallel
parallel -j 4 ./pipeline.sh < opportunities.jsonl > bundles.jsonl
```

### Alternative Formats
Components could support different output formats:
```bash
# Future: Binary output for performance
./pipeline.sh --output-format=msgpack < opportunity.json > bundle.msgpack
```

## Conclusion

This 4-component pipeline provides a clean, modular architecture that:
- Maintains Unix philosophy principles
- Meets performance requirements
- Enables independent testing and development
- Supports debugging and monitoring
- Allows for future optimizations