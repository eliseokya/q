# Compiler Mapping Rules

## Overview

This document defines the exact rules for transforming opportunity JSON into the mathematical DSL. These rules ensure consistent and predictable compilation across all inputs.

## Token Mapping Rules

### Supported Tokens
The DSL supports exactly these tokens from `maths/DSL/Syntax.lean`:
- `ETH`
- `WETH`
- `USDC`
- `DAI`

### Mapping Rules
| Input | Output | Notes |
|-------|--------|-------|
| `"ETH"`, `"eth"`, `"Eth"` | `"ETH"` | Case-insensitive |
| `"WETH"`, `"weth"`, `"Weth"` | `"WETH"` | Wrapped ETH |
| `"USDC"`, `"usdc"`, `"Usdc"` | `"USDC"` | USD Coin |
| `"DAI"`, `"dai"`, `"Dai"` | `"DAI"` | DAI Stablecoin |
| Any other value | Error: `UNKNOWN_TOKEN` | Not supported |

### Custom Tokens
If the input contains `"custom:0x..."`, it maps to `Token.custom(address)` in the DSL.

## Protocol Mapping Rules

### Supported Protocols
From `maths/DSL/Syntax.lean`:
- `Aave`
- `UniswapV2`
- `Compound`

### Mapping Rules
| Input | Output | Notes |
|-------|--------|-------|
| `"aave"`, `"Aave"`, `"AAVE"`, `"aave-v3"` | `"Aave"` | All Aave variants |
| `"uniswap"`, `"uniswapv2"`, `"UniswapV2"`, `"uni"` | `"UniswapV2"` | Uniswap V2 only |
| `"compound"`, `"Compound"`, `"COMPOUND"` | `"Compound"` | Compound protocol |
| `"custom:..."` | `Protocol.custom(name)` | Custom protocols |
| Any other value | Error: `UNKNOWN_PROTOCOL` | Not supported |

### Protocol Availability by Chain
| Protocol | Polygon | Arbitrum |
|----------|---------|----------|
| Aave | ✓ | ✓ |
| UniswapV2 | ✓ | ✓ |
| Compound | ✓ | ✓ |

## Chain Mapping Rules

### Supported Chains
From `maths/Chain.lean`:
- `polygon`
- `arbitrum`

### Mapping Rules
| Input | Output | Notes |
|-------|--------|-------|
| `"polygon"`, `"Polygon"`, `"POLYGON"`, `"matic"` | `"polygon"` | Polygon PoS |
| `"arbitrum"`, `"Arbitrum"`, `"ARBITRUM"`, `"arb"` | `"arbitrum"` | Arbitrum One |
| Any other value | Error: `UNKNOWN_CHAIN` | Not supported |

## Action Mapping Rules

### Action Type Detection
Based on the `action` field in the opportunity JSON:

| Action Value | DSL Action Type | Required Fields |
|--------------|-----------------|-----------------|
| `"borrow"` | `Action.borrow` | amount, token, protocol |
| `"repay"` | `Action.repay` | amount, token, protocol |
| `"swap"` | `Action.swap` | from/amount, to, minOut, protocol |
| `"bridge"` | `Action.bridge` | to, token, amount |
| `"deposit"` | `Action.deposit` | amount, token, protocol |
| `"withdraw"` | `Action.withdraw` | amount, token, protocol |

### Field Mappings by Action Type

#### Borrow
```json
// Input
{"action": "borrow", "amount": "100", "token": "WETH", "protocol": "aave"}

// Output Action
{
  "type": "borrow",
  "amount": {"num": 100, "den": 1},
  "token": "WETH",
  "protocol": "Aave"
}
```

#### Swap
```json
// Input (multiple formats supported)
{"action": "swap", "from": "WETH", "to": "USDC", "amount": "100", "minOut": "150000"}
{"action": "swap", "tokenIn": "WETH", "tokenOut": "USDC", "amountIn": "100", "minAmountOut": "150000"}

// Output Action
{
  "type": "swap",
  "amount_in": {"num": 100, "den": 1},
  "token_in": "WETH",
  "token_out": "USDC",
  "min_out": {"num": 150000, "den": 1},
  "protocol": "UniswapV2"
}
```

Field mappings for swap:
- `from`, `tokenIn` → `token_in`
- `to`, `tokenOut` → `token_out`
- `amount`, `amountIn` → `amount_in`
- `minOut`, `minAmountOut`, `expectedOut` → `min_out`

#### Bridge
```json
// Input
{"action": "bridge", "to": "arbitrum", "token": "WETH", "amount": "100"}

// Output Action
{
  "type": "bridge",
  "from_chain": "polygon",  // Inferred from context
  "to_chain": "arbitrum",
  "token": "WETH",
  "amount": {"num": 100, "den": 1}
}
```

## Amount Conversion Rules

### String to Rational Number
All amounts are converted to rational numbers with numerator and denominator:

| Input | Output | Explanation |
|-------|--------|-------------|
| `"100"` | `{"num": 100, "den": 1}` | Integer |
| `"1.5"` | `{"num": 3, "den": 2}` | Decimal to fraction |
| `"0.1"` | `{"num": 1, "den": 10}` | Small decimal |
| `"123.456"` | `{"num": 123456, "den": 1000}` | Precise decimal |
| `"1e18"` | `{"num": 1000000000000000000, "den": 1}` | Scientific notation |
| `100` | `{"num": 100, "den": 1}` | Already number |

### Special Cases
- Empty string → Error: `INVALID_AMOUNT`
- Non-numeric → Error: `INVALID_AMOUNT`
- Negative → Error: `NEGATIVE_AMOUNT`
- Zero → Allowed but may fail validation later

### Precision Rules
- Maximum 18 decimal places (Ethereum standard)
- Numbers are reduced to lowest terms: `{"num": 50, "den": 100}` → `{"num": 1, "den": 2}`

## Chain Context Inference Rules

### Starting Chain
1. Use `source_chain` from metadata if present
2. Otherwise, use chain of first non-bridge action
3. Default to `"polygon"` if no indication

### Chain Tracking Through Actions
```
Action: borrow on polygon
Current Chain: polygon

Action: bridge to arbitrum
Current Chain: arbitrum (after bridge)

Action: swap (no chain specified)
Current Chain: arbitrum (unchanged)

Action: bridge to polygon
Current Chain: polygon (after bridge)
```

### Chain Assignment Rules
1. Non-bridge actions inherit current chain
2. Bridge actions change current chain to target
3. Actions after bridge are on the bridge's target chain

## Constraint Mapping Rules

### Constraint Types
| JSON Field | DSL Constraint | Value Type |
|------------|----------------|------------|
| `deadline` | `Constraint.deadline` | Number (blocks) |
| `max_gas` | `Constraint.maxGas` | Number (gas units) |
| `min_balance` | `Constraint.minBalance` | Token + Amount |
| `invariants` | `Constraint.invariant` | Array of strings |

### Constraint Extraction
```json
// Input
{
  "constraints": {
    "deadline": 20,
    "max_gas": 1000000,
    "min_balance": {
      "token": "USDC",
      "amount": "100"
    },
    "invariants": ["constant-product"]
  }
}

// Output
[
  {"type": "deadline", "blocks": 20},
  {"type": "maxGas", "amount": 1000000},
  {"type": "minBalance", "token": "USDC", "amount": {"num": 100, "den": 1}},
  {"type": "invariant", "name": "constant-product"}
]
```

### Default Constraints
If no constraints provided:
- No deadline constraint
- No gas limit
- No minimum balance requirements
- No invariants

## Expression Building Rules

### Sequential Composition
Actions are composed right-associatively:
```
[A, B, C] → Seq(A, Seq(B, C))
```

### Parallel Detection Rules
Actions can be parallel if ALL conditions are met:
1. They operate on different chains
2. No data dependencies (output of one isn't input of another)
3. They don't share the same protocol on the same chain
4. They're not borrow/repay pairs (must be sequential)

Example parallel pattern:
```
swap on polygon + swap on arbitrum → Parallel(swap1, swap2)
```

### OnChain Wrapping Rules
Actions are wrapped in `OnChain` when:
1. The action's chain differs from the bundle's startChain
2. The action follows a bridge to a different chain
3. Multiple sequential actions on the same non-start chain

Example:
```
// Start chain: polygon
borrow (polygon) → bridge (arbitrum) → swap (arbitrum) → bridge (polygon) → repay (polygon)

// Becomes:
Seq(
  Action(borrow),
  Seq(
    Action(bridge),
    Seq(
      OnChain(arbitrum, Action(swap)),
      Seq(
        Action(bridge),
        Action(repay)
      )
    )
  )
)
```

## Error Handling Rules

### Error Priority
When multiple errors exist, report the first by priority:
1. JSON syntax errors
2. Missing required fields
3. Type conversion errors
4. Validation errors
5. Logic errors

### Error Context
All errors must include:
- Component that detected the error
- Specific field or action index
- Clear error message
- Suggestion for fix (when possible)

### Recovery Strategy
- No partial compilation - fail fast
- Return error immediately
- Preserve original input in error context

## Bundle Assembly Rules

### Name Generation
- Use `opportunity_id` directly as bundle name
- No transformation or validation of the ID

### Start Chain Determination
1. Use `source_chain` from metadata
2. If not present, use chain of first action
3. Error if no chain can be determined

### Final Validation
Before outputting bundle, verify:
- All expressions properly nested
- All types are valid DSL types
- No null or undefined values
- Constraints array is valid (empty array if no constraints)

## Type Safety Rules

### Enum Validation
All string values must map to valid enum values:
- Token: Must be in `["ETH", "WETH", "USDC", "DAI"]`
- Protocol: Must be in `["Aave", "UniswapV2", "Compound"]`
- Chain: Must be in `["polygon", "arbitrum"]`

### Amount Validation
- Must be positive rational numbers
- Numerator and denominator must be positive integers
- Denominator cannot be zero

### Expression Validation
- All expressions must have required fields
- Nested expressions must be well-formed
- No circular references

## Future Extensions

### Adding New Tokens
1. Update Token enum in mathematical model
2. Add mapping rule in this document
3. Update transform-actions component

### Adding New Protocols
1. Update Protocol enum in mathematical model
2. Add mapping rule with all variants
3. Update protocol availability matrix
4. Update transform-actions component

### Adding New Chains
1. Update Chain enum in mathematical model
2. Add mapping rule with aliases
3. Update protocol availability for new chain
4. Update chain inference logic

### Adding New Actions
1. Update Action type in mathematical model
2. Define required fields
3. Add mapping rules
4. Update all components to handle new action