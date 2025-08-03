# Compiler Output Format Specification

## Overview

The compiler's final output provides the mathematical DSL Bundle structure to the analyzer for pattern matching. Since the compiler and analyzer are part of the same validator system, they can share in-memory representations directly.

## Final Design Decision

After careful consideration of the architecture, the compiler outputs a **JSON representation** of the DSL Bundle that serves as:
1. A structured format for inter-component communication (Unix philosophy)
2. A direct representation of the mathematical DSL types
3. A debuggable intermediate format

## Output Format

The compiler outputs a JSON structure that directly represents the DSL Bundle:

```json
{
  "type": "Bundle",
  "name": "opp_12345",
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
  "constraints": [
    {"type": "deadline", "blocks": 20},
    {"type": "maxGas", "amount": 1000000}
  ]
}
```

## Type Representation

All types map directly to the DSL definitions in `maths/DSL/Syntax.lean`:

### Actions
- `{"type": "borrow", ...}` → `Action.borrow`
- `{"type": "repay", ...}` → `Action.repay`
- `{"type": "swap", ...}` → `Action.swap`
- `{"type": "bridge", ...}` → `Action.bridge`
- `{"type": "deposit", ...}` → `Action.deposit`
- `{"type": "withdraw", ...}` → `Action.withdraw`

### Expressions
- `{"type": "Action", "action": ...}` → `Expr.action`
- `{"type": "Seq", "e1": ..., "e2": ...}` → `Expr.seq`
- `{"type": "Parallel", "e1": ..., "e2": ...}` → `Expr.parallel`
- `{"type": "OnChain", "chain": ..., "expr": ...}` → `Expr.onChain`

### Constraints
- `{"type": "deadline", "blocks": n}` → `Constraint.deadline`
- `{"type": "maxGas", "amount": n}` → `Constraint.maxGas`
- `{"type": "minBalance", "token": ..., "amount": ...}` → `Constraint.minBalance`
- `{"type": "invariant", "name": ...}` → `Constraint.invariant`

### Enumerations
- Token values: `"ETH"`, `"WETH"`, `"USDC"`, `"DAI"`
- Protocol values: `"Aave"`, `"UniswapV2"`, `"Compound"`
- Chain values: `"polygon"`, `"arbitrum"`

### Rational Numbers
All amounts use the rational representation:
```json
{"num": 100, "den": 1}    // Represents 100/1 = 100
{"num": 3, "den": 2}      // Represents 3/2 = 1.5
{"num": 1, "den": 10}     // Represents 1/10 = 0.1
```

## Pattern Matching in the Analyzer

The analyzer will parse this JSON into the actual DSL structures for pattern matching:

```rust
// Pseudo-code for the analyzer
let bundle: Bundle = parse_json(input)?;

match bundle.expr {
    Expr::Seq(
        Expr::Action(Action::Borrow { amount, token, protocol }),
        Expr::Seq(middle, 
            Expr::Action(Action::Repay { amount: amount2, token: token2, protocol: protocol2 })
        )
    ) if amount == amount2 && token == token2 && protocol == protocol2 => {
        // Flash loan pattern matched!
        Pattern::FlashLoan { amount, token, protocol, middle_operations: middle }
    }
    _ => {
        // Try other patterns...
    }
}
```

## Benefits of JSON Output

1. **Debuggability**: Can inspect compiler output easily
2. **Testability**: Easy to create test fixtures
3. **Flexibility**: Can modify without recompiling
4. **Standardization**: JSON is universally supported
5. **Type Clarity**: Explicit type annotations

## Integration with Analyzer

The analyzer receives this JSON and:
1. Parses it into internal DSL structures
2. Validates the structure matches DSL types
3. Performs pattern matching on the typed structures
4. Returns matched patterns with parameters

## Validation Rules

The JSON output must satisfy:
- All required fields present
- Type fields match valid DSL types
- Amounts are valid rationals (positive numerator and denominator)
- Tokens, protocols, and chains are from the allowed set
- Expression tree is well-formed
- Constraints are properly typed

## Error Representation

If compilation fails, output an error instead:
```json
{
  "error": true,
  "component": "assemble-bundle",
  "code": "INVALID_EXPRESSION",
  "message": "Expression tree is malformed",
  "context": {
    "location": "expr.e2.e2",
    "issue": "Missing required field 'action'"
  }
}
```

## Example: Complete Flash Loan

Input opportunity:
```json
{
  "opportunity_id": "flash_loan_001",
  "path": [
    {"action": "borrow", "amount": "1000", "token": "USDC", "protocol": "aave"},
    {"action": "swap", "from": "USDC", "to": "WETH", "amount": "1000", "minOut": "0.5"},
    {"action": "swap", "from": "WETH", "to": "USDC", "amount": "0.5", "minOut": "1050"},
    {"action": "repay", "amount": "1000", "token": "USDC", "protocol": "aave"}
  ]
}
```

Compiler output:
```json
{
  "type": "Bundle",
  "name": "flash_loan_001",
  "startChain": "polygon",
  "expr": {
    "type": "Seq",
    "e1": {
      "type": "Action",
      "action": {
        "type": "borrow",
        "amount": {"num": 1000, "den": 1},
        "token": "USDC",
        "protocol": "Aave"
      }
    },
    "e2": {
      "type": "Seq",
      "e1": {
        "type": "Action",
        "action": {
          "type": "swap",
          "amount_in": {"num": 1000, "den": 1},
          "token_in": "USDC",
          "token_out": "WETH",
          "min_out": {"num": 1, "den": 2},
          "protocol": "UniswapV2"
        }
      },
      "e2": {
        "type": "Seq",
        "e1": {
          "type": "Action",
          "action": {
            "type": "swap",
            "amount_in": {"num": 1, "den": 2},
            "token_in": "WETH",
            "token_out": "USDC",
            "min_out": {"num": 1050, "den": 1},
            "protocol": "UniswapV2"
          }
        },
        "e2": {
          "type": "Action",
          "action": {
            "type": "repay",
            "amount": {"num": 1000, "den": 1},
            "token": "USDC",
            "protocol": "Aave"
          }
        }
      }
    }
  },
  "constraints": []
}
```

This output directly represents the mathematical DSL structure and is ready for pattern matching by the analyzer.