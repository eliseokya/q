# Compiler Data Flow Specification

## Overview

This document specifies the exact data formats and transformations at each stage of the 4-component compiler pipeline. Each component performs a specific transformation, progressively converting untyped JSON into the typed DSL Bundle structure.

## Pipeline Overview

```
Opportunity JSON → parse-and-validate → transform-actions → build-expression → assemble-bundle → DSL Bundle
```

## Stage 0: Input Format (Opportunity JSON)

**Source**: Detection system
**Format**: Raw JSON text

```json
{
  "opportunity_id": "opp_12345_1234567890",
  "timestamp": "2024-08-03T12:34:56Z",
  "source_chain": "polygon",
  "target_chain": "arbitrum",
  "path": [
    {
      "action": "borrow",
      "amount": "100",
      "token": "WETH",
      "protocol": "aave"
    },
    {
      "action": "bridge",
      "to": "arbitrum",
      "token": "WETH",
      "amount": "100"
    },
    {
      "action": "swap",
      "from": "WETH",
      "to": "USDC",
      "amount": "100",
      "minOut": "150000",
      "protocol": "uniswap"
    },
    {
      "action": "bridge",
      "to": "polygon",
      "token": "USDC",
      "amount": "150000"
    },
    {
      "action": "repay",
      "amount": "100",
      "token": "WETH",
      "protocol": "aave"
    }
  ],
  "expected_profit": "500",
  "confidence": 0.95,
  "constraints": {
    "deadline": 20,
    "max_gas": 1000000
  }
}
```

**Variations**:
- Amount can be string or number: `"100"` or `100`
- Protocol names are case-insensitive: `"aave"`, `"Aave"`, `"AAVE"`
- Constraints object is optional
- Additional fields may be present and are preserved

## Stage 1: After parse-and-validate

**Purpose**: Validated structure with extracted components

```json
{
  "metadata": {
    "opportunity_id": "opp_12345_1234567890",
    "source_chain": "polygon",
    "target_chain": "arbitrum",
    "timestamp": "2024-08-03T12:34:56Z",
    "expected_profit": "500",
    "confidence": 0.95
  },
  "actions": [
    {
      "action": "borrow",
      "amount": "100",
      "token": "WETH",
      "protocol": "aave"
    },
    {
      "action": "bridge",
      "to": "arbitrum",
      "token": "WETH",
      "amount": "100"
    },
    {
      "action": "swap",
      "from": "WETH",
      "to": "USDC",
      "amount": "100",
      "minOut": "150000",
      "protocol": "uniswap"
    },
    {
      "action": "bridge",
      "to": "polygon",
      "token": "USDC",
      "amount": "150000"
    },
    {
      "action": "repay",
      "amount": "100",
      "token": "WETH",
      "protocol": "aave"
    }
  ],
  "constraints": {
    "deadline": 20,
    "max_gas": 1000000,
    "min_balance": null,
    "invariants": []
  }
}
```

**Transformations Applied**:
- Top-level structure reorganized into metadata/actions/constraints
- All amounts normalized to strings (if they weren't already)
- Missing constraint fields added with null/empty defaults
- Metadata preserves all non-action fields

## Stage 2: After transform-actions

**Purpose**: Typed and normalized action data

```json
{
  "metadata": {
    "opportunity_id": "opp_12345_1234567890",
    "source_chain": "polygon",
    "target_chain": "arbitrum",
    "timestamp": "2024-08-03T12:34:56Z",
    "expected_profit": "500",
    "confidence": 0.95
  },
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
    },
    {
      "type": "bridge",
      "from_chain": "arbitrum",
      "to_chain": "polygon",
      "token": "USDC",
      "amount": {"num": 150000, "den": 1}
    },
    {
      "type": "repay",
      "amount": {"num": 100, "den": 1},
      "token": "WETH",
      "protocol": "Aave",
      "chain": "polygon"
    }
  ],
  "constraints": {
    "deadline": 20,
    "max_gas": 1000000,
    "min_balance": null,
    "invariants": []
  }
}
```

**Transformations Applied**:
- All amounts converted to rational numbers `{"num": n, "den": d}`
- Token strings mapped to canonical form: `"weth" → "WETH"`
- Protocol strings mapped to canonical form: `"aave" → "Aave"`, `"uniswap" → "UniswapV2"`
- Chain context inferred and added to each action
- Bridge actions have explicit `from_chain` and `to_chain`
- Swap actions have fields renamed: `from → token_in`, `to → token_out`, `amount → amount_in`
- Action type explicitly added as `"type"` field

**Rational Number Examples**:
- `"100"` → `{"num": 100, "den": 1}`
- `"1.5"` → `{"num": 3, "den": 2}`
- `"0.1"` → `{"num": 1, "den": 10}`
- `"123.456"` → `{"num": 123456, "den": 1000}`

## Stage 3: After build-expression

**Purpose**: Expression tree with optimization

```json
{
  "metadata": {
    "opportunity_id": "opp_12345_1234567890",
    "source_chain": "polygon",
    "target_chain": "arbitrum",
    "timestamp": "2024-08-03T12:34:56Z",
    "expected_profit": "500",
    "confidence": 0.95
  },
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
        "type": "Seq",
        "e1": {
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
        },
        "e2": {
          "type": "Seq",
          "e1": {
            "type": "Action",
            "action": {
              "type": "bridge",
              "chain": "polygon",
              "token": "USDC",
              "amount": {"num": 150000, "den": 1}
            }
          },
          "e2": {
            "type": "Action",
            "action": {
              "type": "repay",
              "amount": {"num": 100, "den": 1},
              "token": "WETH",
              "protocol": "Aave"
            }
          }
        }
      }
    }
  },
  "constraints": {
    "deadline": 20,
    "max_gas": 1000000,
    "min_balance": null,
    "invariants": []
  }
}
```

**Transformations Applied**:
- Actions wrapped in Expression nodes
- Sequential actions composed with `Expr.Seq` (right-associative)
- Chain-specific actions wrapped in `Expr.OnChain`
- Parallel opportunities identified (though not present in this example)
- Bridge actions simplified to just target chain

**Expression Types**:
- `{"type": "Action", "action": {...}}` - Single action
- `{"type": "Seq", "e1": ..., "e2": ...}` - Sequential composition
- `{"type": "Parallel", "e1": ..., "e2": ...}` - Parallel composition
- `{"type": "OnChain", "chain": "...", "expr": ...}` - Chain context

**Parallel Example** (when applicable):
```json
{
  "type": "Parallel",
  "e1": {
    "type": "OnChain",
    "chain": "polygon",
    "expr": {"type": "Action", "action": {...}}
  },
  "e2": {
    "type": "OnChain", 
    "chain": "arbitrum",
    "expr": {"type": "Action", "action": {...}}
  }
}
```

## Stage 4: Final Output (After assemble-bundle)

**Purpose**: Complete DSL Bundle

```json
{
  "type": "Bundle",
  "name": "opp_12345_1234567890",
  "startChain": "polygon",
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
        "type": "Seq",
        "e1": {
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
        },
        "e2": {
          "type": "Seq",
          "e1": {
            "type": "Action",
            "action": {
              "type": "bridge",
              "chain": "polygon",
              "token": "USDC",
              "amount": {"num": 150000, "den": 1}
            }
          },
          "e2": {
            "type": "Action",
            "action": {
              "type": "repay",
              "amount": {"num": 100, "den": 1},
              "token": "WETH",
              "protocol": "Aave"
            }
          }
        }
      }
    }
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

**Transformations Applied**:
- Bundle structure created with type annotation
- Name taken from opportunity_id
- StartChain determined from metadata or first action
- Expression tree included as-is
- Constraints converted to array format with type annotations
- Null constraints filtered out

**Constraint Types**:
- `{"type": "deadline", "blocks": n}`
- `{"type": "maxGas", "amount": n}`
- `{"type": "minBalance", "token": "...", "amount": {"num": n, "den": d}}`
- `{"type": "invariant", "name": "..."}`

## Type Mappings Summary

### Tokens
- `"ETH"` → `"ETH"`
- `"WETH"`, `"weth"` → `"WETH"`
- `"USDC"`, `"usdc"` → `"USDC"`
- `"DAI"`, `"dai"` → `"DAI"`
- Unknown tokens → Error

### Protocols
- `"aave"`, `"Aave"`, `"AAVE"` → `"Aave"`
- `"uniswap"`, `"uniswapv2"`, `"UniswapV2"` → `"UniswapV2"`
- `"compound"`, `"Compound"` → `"Compound"`
- Unknown protocols → Error

### Chains
- `"polygon"`, `"matic"` → `"polygon"`
- `"arbitrum"`, `"arb"` → `"arbitrum"`
- Unknown chains → Error

### Actions
- `"borrow"` → Creates `Action.borrow`
- `"repay"` → Creates `Action.repay`
- `"swap"` → Creates `Action.swap`
- `"bridge"` → Creates `Action.bridge`
- `"deposit"` → Creates `Action.deposit`
- `"withdraw"` → Creates `Action.withdraw`

## Error Handling

Errors halt the pipeline and are output to stderr:

```json
{
  "error": true,
  "component": "transform-actions",
  "code": "INVALID_AMOUNT",
  "message": "Cannot parse amount: 'abc'",
  "context": {
    "action_index": 2,
    "field": "amount",
    "value": "abc"
  },
  "suggestion": "Amount must be a valid number"
}
```

**Common Error Codes**:
- `MALFORMED_JSON` - Invalid JSON syntax
- `MISSING_FIELD` - Required field missing
- `UNKNOWN_TOKEN` - Token not in supported list
- `UNKNOWN_PROTOCOL` - Protocol not supported
- `UNKNOWN_CHAIN` - Chain not supported
- `INVALID_AMOUNT` - Amount cannot be parsed
- `CHAIN_MISMATCH` - Protocol not available on chain
- `INVALID_CONSTRAINT` - Constraint value invalid

## Performance Considerations

### Data Size Growth
- Input: ~1KB typical opportunity JSON
- After parse-and-validate: ~1.2KB (structure reorganization)
- After transform-actions: ~1.5KB (rational numbers)
- After build-expression: ~2KB (expression tree)
- Final output: ~2.2KB (complete bundle)

### Critical Transformations
1. **String to Rational**: Most compute-intensive in transform-actions
2. **Parallel Analysis**: Most complex logic in build-expression
3. **Tree Building**: Recursive structure creation in build-expression

### Memory Efficiency
- Streaming JSON parsing where possible
- Minimal intermediate allocations
- Share string references instead of copying

## Validation Rules

### parse-and-validate
- Must have `opportunity_id` field
- Must have `path` array with at least one action
- Each action must have `action` field
- JSON must be syntactically valid

### transform-actions
- All amounts must be parseable as numbers
- All tokens must be in the supported set
- All protocols must be recognized
- Bridge actions must have valid source/target chains

### build-expression
- First and last actions must be on the same chain
- Bridge actions must connect sequential chain contexts
- Parallel actions must be truly independent

### assemble-bundle
- Bundle must have all required fields
- Expression tree must be well-formed
- Constraints must have valid values

## Testing Scenarios

### Happy Path
- Simple flash loan (borrow → swap → repay)
- Cross-chain arbitrage (with bridges)
- Parallel operations (independent swaps)
- Complex multi-hop paths

### Error Cases
- Malformed JSON
- Unknown tokens/protocols
- Invalid amounts
- Missing required fields
- Incompatible action sequences

### Edge Cases
- Empty constraints object
- Single action path
- Very large amounts (overflow testing)
- Deep nesting (performance testing)