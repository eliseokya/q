# Validator - Higher Level Design

## Overview

The Validator is responsible for mathematically validating incoming arbitrage opportunities against pre-proven patterns from our categorical model. It consists of four sequential modules, each with a single input and single output, following the Unix philosophy of "do one thing well."

## Architecture

```
Opportunity JSON → Compiler → Analyzer → Proof Verifier → Bundle Generator → Validated Bundle JSON
                      ↓          ↓            ↓                ↓
                  JSON→DSL    Pattern      Verify          Generate
                             Matching    Constraints    Execution Plan
```

## Key Insight

The Validator does NOT compile a Domain Specific Language (DSL). Instead, it:
1. **Compiles TO** the existing mathematical DSL (defined in `maths/DSL/Syntax.lean`)
2. **Validates** against pre-proven patterns
3. **Generates** execution bundles

## Module Specifications

### 1. Compiler Module

**Purpose**: Compile raw opportunity JSON from the detection system into the mathematical DSL defined in our Lean 4 model.

**Input**: Opportunity JSON
```json
{
  "opportunity_id": "opp_123",
  "timestamp": 1234567890,
  "source_chain": "ethereum",
  "operations": [
    {"action": "borrow", "protocol": "aave", "token": "USDC", "amount": "100000"},
    {"action": "swap", "protocol": "uniswap", "from": "USDC", "to": "ETH"},
    {"action": "bridge", "to": "arbitrum", "token": "ETH"},
    {"action": "swap", "protocol": "sushiswap", "from": "ETH", "to": "USDC"},
    {"action": "bridge", "to": "ethereum", "token": "USDC"},
    {"action": "repay", "protocol": "aave", "token": "USDC", "amount": "100000"}
  ],
  "expected_profit": "500"
}
```

**Output**: DSL Expression (following `maths/DSL/Syntax.lean`)
```json
{
  "dsl_version": "1.0",
  "opportunity_id": "opp_123",
  "timestamp": 1234567890,
  "expr": {
    "type": "Expr.seq",
    "first": {
      "type": "Expr.action",
      "action": {
        "type": "Action.borrow",
        "amount": 100000,
        "token": "Token.USDC",
        "protocol": "Protocol.Aave"
      }
    },
    "rest": {
      "type": "Expr.seq",
      "first": {
        "type": "Expr.action",
        "action": {
          "type": "Action.swap",
          "amountIn": 100000,
          "tokenIn": "Token.USDC",
          "tokenOut": "Token.ETH",
          "minOut": 0,
          "protocol": "Protocol.UniswapV2"
        }
      },
      "rest": "..."
    }
  },
  "bundle": {
    "name": "cross-chain-arb-123",
    "startChain": "Chain.ethereum",
    "constraints": [
      {"type": "Constraint.deadline", "blocks": 20}
    ]
  }
}
```

**Key Responsibilities**:
- JSON parsing and validation
- Mapping JSON actions to DSL Actions
- Constructing DSL Expressions (Expr)
- Inferring missing information (chains, protocols)
- Creating Bundle structure with constraints

**Transformation Rules**:
- `"borrow"` → `Action.borrow`
- `"swap"` → `Action.swap`
- `"bridge"` → `Action.bridge`
- Sequential operations → `Expr.seq`
- Operations on same chain → can use `Expr.parallel`

---

### 2. Analyzer Module

**Purpose**: Analyze the DSL expression to identify which pre-proven pattern it matches and extract pattern parameters.

**Input**: DSL Expression from Compiler

**Output**: Matched Pattern
```json
{
  "pattern_id": "cross-chain-arbitrage",
  "pattern_name": "Cross-Chain Flash Loan Arbitrage",
  "pattern_version": "1.0",
  "proof_certificate": "maths/DSL/Patterns/CrossChainArb.proof",
  "pattern_structure": {
    "type": "FlashLoanCrossChain",
    "components": [
      {"step": 1, "pattern": "borrow", "matched": true},
      {"step": 2, "pattern": "bridge", "matched": true},
      {"step": 3, "pattern": "swap", "matched": true},
      {"step": 4, "pattern": "bridge_back", "matched": true},
      {"step": 5, "pattern": "repay", "matched": true}
    ]
  },
  "pattern_parameters": {
    "$SOURCE_CHAIN": "ethereum",
    "$TARGET_CHAIN": "arbitrum",
    "$BORROW_TOKEN": "USDC",
    "$BORROW_AMOUNT": 100000,
    "$INTERMEDIATE_TOKEN": "ETH",
    "$BORROW_PROTOCOL": "Aave",
    "$SOURCE_DEX": "UniswapV2",
    "$TARGET_DEX": "Sushiswap"
  },
  "dsl_expr": { /* Original DSL expression included */ },
  "matching_confidence": 1.0,
  "pattern_library_ref": "maths/DSL/Patterns/Library.lean"
}
```

**Key Responsibilities**:
- Pattern library management (pre-proven patterns from Lean)
- Structural pattern matching against DSL expressions
- Parameter extraction from matched patterns
- Pattern versioning and compatibility
- Confidence scoring for matches

**Pattern Library**: Lives in this module, contains references to Lean proofs in `maths/DSL/Patterns/`

---

### 3. Proof Verifier Module

**Purpose**: Verify that the matched pattern with its specific parameters satisfies all mathematical constraints and that the proof certificate is valid.

**Input**: Matched Pattern from Analyzer

**Output**: Verified Pattern
```json
{
  "verification_id": "verify_123",
  "pattern_id": "cross-chain-arbitrage",
  "verified": true,
  "timestamp": 1234567891,
  "mathematical_checks": {
    "proof_certificate": {
      "valid": true,
      "location": "maths/DSL/Patterns/CrossChainArb.proof",
      "theorem": "CrossChainArbPattern_is_atomic"
    },
    "pattern_instantiation": {
      "valid": true,
      "details": "All parameters match theorem preconditions"
    },
    "atomicity": {
      "verified": true,
      "details": "Forms invertible 2-cell in bicategory of chains"
    }
  },
  "constraint_checks": {
    "value_preservation": {
      "passed": true,
      "details": "Borrow amount equals repay amount: 100000 USDC"
    },
    "timing_feasibility": {
      "passed": true,
      "details": "All operations completable within deadline (20 blocks)"
    },
    "bridge_validity": {
      "passed": true,
      "details": "Bridges available: ETH ethereum→arbitrum, USDC arbitrum→ethereum"
    },
    "gas_feasibility": {
      "passed": true,
      "details": "Estimated gas: $45, Expected profit: $500, Net profit: $455"
    },
    "protocol_availability": {
      "passed": true,
      "details": "All protocols (Aave, Uniswap, Sushiswap) available on respective chains"
    }
  },
  "matched_pattern": { /* Original matched pattern included */ }
}
```

**Key Responsibilities**:
- Verify Lean proof certificates are valid
- Check pattern instantiation satisfies theorem preconditions
- Validate all mathematical constraints from the model
- Real-time feasibility checks (gas, timing, liquidity)
- Detailed failure reporting for debugging

**Mathematical Verification**: References proofs in `maths/` but doesn't reprove them

---

### 4. Bundle Generator Module

**Purpose**: Transform the verified pattern into an executable bundle with all concrete details needed for the execution tools.

**Input**: Verified Pattern from Proof Verifier

**Output**: Execution Bundle JSON
```json
{
  "bundle_id": "bundle_123",
  "opportunity_id": "opp_123",
  "pattern_id": "cross-chain-arbitrage",
  "created_at": 1234567892,
  "deadline": 1234568192,
  "mathematical_properties": {
    "is_atomic": true,
    "proof_reference": "maths/DSL/Patterns/CrossChainArb.proof",
    "verified_at": 1234567891
  },
  "execution_plan": {
    "total_steps": 6,
    "estimated_duration": 180,
    "steps": [
      {
        "step": 1,
        "operation": "flashloan",
        "chain": "ethereum",
        "contract": "0x7d2768dE32b0b80b7a3454c06BdAc94A69DDc7A9",
        "function": "flashLoan",
        "params": {
          "receiverAddress": "0xExecutorContract",
          "assets": ["0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48"],
          "amounts": ["100000000000"],
          "modes": [0],
          "onBehalfOf": "0xExecutorContract",
          "params": "0x...",
          "referralCode": 0
        },
        "gas_estimate": 150000
      },
      {
        "step": 2,
        "operation": "swap",
        "chain": "ethereum",
        "protocol": "uniswap_v2",
        "contract": "0x7a250d5630B4cF539739dF2C5dAcb4c659F2488D",
        "function": "swapExactTokensForTokens",
        "params": {
          "amountIn": "100000000000",
          "amountOutMin": "0",
          "path": ["0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48", "0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2"],
          "to": "0xExecutorContract",
          "deadline": 1234568192
        },
        "gas_estimate": 120000
      },
      {
        "step": 3,
        "operation": "bridge",
        "chain": "ethereum",
        "bridge": "atomic_mesh_bridge",
        "contract": "0xAtomicMeshBridge",
        "function": "bridgeTokens",
        "params": {
          "token": "0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2",
          "amount": "dynamic:step2.output",
          "targetChain": 42161,
          "targetAddress": "0xExecutorContractArbitrum",
          "data": "0x..."
        },
        "gas_estimate": 200000
      }
      /* ... remaining steps ... */
    ]
  },
  "gas_config": {
    "total_gas_estimate": 750000,
    "max_gas_price": "50000000000",
    "priority_fee": "2000000000",
    "gas_buffer_percent": 20
  },
  "profit_config": {
    "expected_gross_profit": "500000000",
    "estimated_gas_cost": "45000000",
    "expected_net_profit": "455000000",
    "min_acceptable_profit": "100000000",
    "profit_token": "USDC",
    "profit_recipient": "0xProfitReceiver"
  },
  "contracts": {
    "ethereum": {
      "executor": "0xAtomicMeshExecutor",
      "flashloan_adapter": "0xAaveAdapter",
      "swap_router": "0xUniswapRouter"
    },
    "arbitrum": {
      "executor": "0xAtomicMeshExecutorArb",
      "swap_router": "0xSushiswapRouter"
    }
  },
  "fallback_options": {
    "alternative_bridges": ["stargate", "across"],
    "alternative_dexes": ["curve", "balancer"]
  }
}
```

**Key Responsibilities**:
- Contract address resolution for all protocols
- Parameter encoding for smart contract calls
- Dynamic value calculation (e.g., swap outputs)
- Gas estimation with safety buffers
- Deadline calculation based on current block
- Execution order optimization
- Fallback options generation

## Data Flow Principles

1. **Single Responsibility**: Each module has one clear purpose
2. **Single Input/Output**: Each module accepts one input type and produces one output type
3. **Stateless**: Modules don't maintain state between invocations
4. **Deterministic**: Same input always produces same output
5. **Error Propagation**: Errors result in explicit failure outputs, not exceptions

## Module Communication

All inter-module communication happens through well-defined JSON structures. Each module can be run independently:

```bash
# Test individual modules
echo $OPPORTUNITY_JSON | ./compiler/bin/compile
echo $DSL_JSON | ./analyzer/bin/analyze  
echo $MATCHED_PATTERN_JSON | ./proof-verifier/bin/verify
echo $VERIFIED_PATTERN_JSON | ./bundle-generator/bin/generate

# Or run the complete pipeline
echo $OPPORTUNITY_JSON | ./validator/pipeline/validate
```

## Error Handling

Each module outputs an error response instead of its normal output on failure:

```json
{
  "error": true,
  "module": "analyzer",
  "error_type": "pattern_not_found",
  "error_message": "No matching pattern for DSL expression",
  "details": {
    "expr_type": "complex_sequence",
    "operation_count": 8,
    "unmatched_operations": ["custom_protocol_call"]
  },
  "input_summary": "8 operations across 3 chains",
  "timestamp": 1234567890
}
```

## Performance Targets

- Compiler: < 2ms (JSON → DSL transformation)
- Analyzer: < 5ms (pattern matching against library)
- Proof Verifier: < 10ms (constraint validation)
- Bundle Generator: < 3ms (bundle creation)
- **Total Pipeline**: < 20ms for 95% of opportunities

## Integration with Mathematical Model

The Validator is tightly integrated with the mathematical model in `maths/`:

1. **Compiler** targets the DSL syntax defined in `maths/DSL/Syntax.lean`
2. **Analyzer** uses patterns proven in `maths/DSL/Patterns/`
3. **Proof Verifier** references theorems from `maths/Grothendieck/` and `maths/Bridge/`
4. **Bundle Generator** uses compilation strategies from `maths/DSL/Compile.lean`

## Future Extensibility

The modular design allows for:
- New patterns can be proven in Lean and added to the Analyzer
- New constraint types can be added to the Proof Verifier
- New protocols can be added to the Bundle Generator
- Compiler can support new opportunity formats from detection system