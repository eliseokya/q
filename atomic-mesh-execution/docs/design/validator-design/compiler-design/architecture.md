# Compiler Module Architecture

## Overview

The compiler is the first module in the validator pipeline, responsible for transforming opportunity JSON from the detection system into the mathematical Domain Specific Language (DSL) defined in `maths/DSL/Syntax.lean`. 

This design follows Unix philosophy while balancing practical performance requirements, resulting in a 4-component pipeline that achieves modularity without sacrificing efficiency.

## Design Principles

1. **Single Responsibility**: Each component has one clear, well-defined purpose
2. **Text Streams**: Components communicate via JSON text streams (stdin/stdout)
3. **Fail Fast**: Errors are detected early and propagated with clear messages
4. **Type Progressive**: Gradual transformation from untyped JSON to typed DSL
5. **Optimization Aware**: Identifies and leverages parallel execution opportunities

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

**Input**: Raw JSON text from stdin
```json
{
  "opportunity_id": "opp_123",
  "source_chain": "polygon",
  "target_chain": "arbitrum",
  "path": [
    {"action": "borrow", "amount": "100", "token": "WETH", "protocol": "aave"},
    {"action": "bridge", "to": "arbitrum", "token": "WETH", "amount": "100"},
    {"action": "swap", "from": "WETH", "to": "USDC", "amount": "100", "minOut": "150000"}
  ],
  "constraints": {
    "deadline": 20,
    "max_gas": 1000000
  }
}
```

**Output**: Validated and structured JSON
```json
{
  "metadata": {
    "opportunity_id": "opp_123",
    "source_chain": "polygon",
    "target_chain": "arbitrum"
  },
  "actions": [
    {"action": "borrow", "amount": "100", "token": "WETH", "protocol": "aave"},
    {"action": "bridge", "to": "arbitrum", "token": "WETH", "amount": "100"},
    {"action": "swap", "from": "WETH", "to": "USDC", "amount": "100", "minOut": "150000"}
  ],
  "constraints": {
    "deadline": 20,
    "max_gas": 1000000,
    "min_balance": null,
    "invariants": []
  }
}
```

**Responsibilities**:
- JSON syntax validation
- Required field validation
- Extract metadata (opportunity_id, chains)
- Extract actions array
- Extract and normalize constraints
- Add default values for optional fields

**Error Cases**:
- Malformed JSON
- Missing required fields (opportunity_id, path)
- Invalid field types
- Empty action array

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
    {
      "type": "bridge",
      "from_chain": "polygon",
      "to_chain": "arbitrum",
      "token": "WETH",
      "amount": {"num": 100, "den": 1}
    },
    {
      "type": "swap",
      "amount_in": {"num": 100, "den": 1},
      "token_in": "WETH",
      "token_out": "USDC",
      "min_out": {"num": 150000, "den": 1},
      "protocol": "UniswapV2",
      "chain": "arbitrum"
    }
  ],
  "constraints": [...]
}
```

**Responsibilities**:
- Convert string amounts to rational numbers {num, den}
- Map token strings to Token enum values ("WETH" → Token.WETH)
- Map protocol strings to Protocol enum values ("aave" → Protocol.Aave)
- Infer chain context from bridge actions
- Track current chain through action sequence
- Validate token/protocol support
- Validate chain/protocol compatibility

**Transformations**:
| Input | Output |
|-------|--------|
| "100" | {"num": 100, "den": 1} |
| "1.5" | {"num": 3, "den": 2} |
| "weth" | "WETH" |
| "aave" | "Aave" |
| "uniswap" | "UniswapV2" |

**Error Cases**:
- Unknown token
- Unknown protocol
- Unsupported chain
- Invalid amount format
- Protocol not available on chain

### 3. build-expression

**Purpose**: Analyze actions and build optimized expression tree

**Input**: Transformed data from transform-actions

**Output**: Data with expression tree
```json
{
  "metadata": {...},
  "expr": {
    "type": "Seq",
    "e1": {
      "type": "Action",
      "action": {
        "type": "borrow",
        "amount": {"num": 100, "den": 1},
        "token": "WETH",
        "protocol": "Aave"
      }
    },
    "e2": {
      "type": "Seq",
      "e1": {
        "type": "Action",
        "action": {
          "type": "bridge",
          "chain": "arbitrum",
          "token": "WETH",
          "amount": {"num": 100, "den": 1}
        }
      },
      "e2": {
        "type": "OnChain",
        "chain": "arbitrum",
        "expr": {
          "type": "Action",
          "action": {
            "type": "swap",
            "amount_in": {"num": 100, "den": 1},
            "token_in": "WETH",
            "token_out": "USDC",
            "min_out": {"num": 150000, "den": 1},
            "protocol": "UniswapV2"
          }
        }
      }
    }
  },
  "constraints": [...]
}
```

**Responsibilities**:
- Identify parallel execution opportunities
- Build Expr.seq for sequential actions
- Build Expr.parallel for independent actions
- Add Expr.onChain wrappers for chain-specific actions
- Optimize expression structure for gas efficiency
- Ensure proper nesting of expressions

**Parallel Detection Logic**:
Actions can execute in parallel if:
- They operate on different chains
- They use different protocols with no shared state
- They have no data dependencies (output of one isn't input to another)
- They don't violate atomicity requirements

**Expression Building Rules**:
- Sequential by default
- Wrap chain-specific actions in Expr.onChain
- Group parallel actions in Expr.parallel
- Right-associate sequential compositions

### 4. assemble-bundle

**Purpose**: Create final DSL Bundle structure

**Input**: Data with expression tree from build-expression

**Output**: Complete DSL Bundle (as JSON representation for the analyzer)
```json
{
  "type": "Bundle",
  "name": "opp_123",
  "startChain": "polygon",
  "expr": {
    "type": "Seq",
    "e1": {...},
    "e2": {...}
  },
  "constraints": [
    {
      "type": "deadline",
      "blocks": 20
    },
    {
      "type": "maxGas",
      "amount": 1000000
    }
  ]
}
```

**Responsibilities**:
- Create Bundle structure with all required fields
- Set name from opportunity_id
- Set startChain from first action or metadata
- Include complete expression tree
- Format constraints in final form
- Validate bundle completeness
- Ensure all types match DSL specification

**Final Type Mappings**:
- All amounts as rationals
- All tokens as Token enum values
- All protocols as Protocol enum values
- All chains as Chain enum values
- All expressions properly typed

## Error Handling

Each component outputs errors in a consistent format:

```json
{
  "error": true,
  "component": "transform-actions",
  "code": "UNKNOWN_TOKEN",
  "message": "Unknown token: 'WBTC'",
  "context": {
    "action_index": 2,
    "action_type": "swap"
  },
  "suggestion": "Supported tokens: ETH, WETH, USDC, DAI"
}
```

The pipeline stops at the first error, and the error is propagated to stderr.

## Performance Requirements

| Component | Target Latency | Max Memory | Critical Path |
|-----------|---------------|------------|---------------|
| parse-and-validate | < 0.3ms | 2MB | Yes |
| transform-actions | < 0.4ms | 3MB | Yes |
| build-expression | < 0.6ms | 5MB | Yes |
| assemble-bundle | < 0.2ms | 2MB | Yes |
| **Total Pipeline** | **< 1.5ms** | **~10MB** | - |

## Inter-Component Communication

All components communicate via JSON through stdin/stdout:

```bash
# Individual component testing
echo '{"test": "data"}' | ./bin/parse-and-validate

# Full pipeline
cat opportunity.json | \
  ./bin/parse-and-validate | \
  ./bin/transform-actions | \
  ./bin/build-expression | \
  ./bin/assemble-bundle > bundle.json
```

## Implementation Guidelines

### Language Choice
**Rust** is recommended for all components:
- Excellent JSON handling with serde
- Strong type system matching DSL types
- Memory safety guarantees
- Predictable performance
- Small binary size
- Good error handling with Result<T, E>

### Shared Code
Common types and utilities are shared via the `common/` module:
- `types.rs`: DSL type definitions
- `errors.rs`: Error type hierarchy
- `rational.rs`: Rational number implementation

### Testing Strategy
Each component should have:
- Unit tests for individual functions
- Integration tests for the complete component
- Property-based tests for transformations
- Benchmark tests for performance validation

## Design Rationale

### Why 4 Components?

We started with 12 fine-grained components but consolidated to 4 for practical reasons:
- **Reduced process overhead**: Fewer process boundaries
- **Simpler deployment**: Only 4 binaries to manage
- **Better performance**: Less IPC overhead
- **Easier debugging**: Clearer component boundaries

### Why JSON Communication?

Despite the overhead, JSON provides:
- **Debuggability**: Can inspect intermediate outputs
- **Language independence**: Components could be rewritten
- **Testability**: Easy to create test fixtures
- **Flexibility**: Can modify pipeline without recompilation

### Why Not Direct Function Calls?

Separate processes provide:
- **Fault isolation**: One component crash doesn't kill pipeline
- **Resource isolation**: Memory limits per component
- **Parallel development**: Teams can work independently
- **Unix philosophy**: Composable tools

## Future Considerations

### Potential Optimizations
1. **Binary protocol**: For production, consider Protocol Buffers
2. **Shared memory**: For high-frequency execution
3. **Component fusion**: Merge components if latency critical

### Extension Points
1. **New tokens**: Add to Token enum in types.rs
2. **New protocols**: Add to Protocol enum
3. **New chains**: Add to Chain enum
4. **New actions**: Extend Action type and update all components

### Monitoring Integration
Each component should emit metrics:
- Processing time
- Memory usage
- Error rates
- Input/output sizes

## Conclusion

This 4-component architecture achieves the right balance between modularity and practicality. It maintains Unix philosophy principles while meeting strict performance requirements, and provides a solid foundation for the validator's compilation needs.