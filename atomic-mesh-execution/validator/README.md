# Validator - Mathematical Validation Layer

## Overview

The Validator is responsible for mathematically validating arbitrage opportunities discovered by the detection system. It validates these opportunities against pre-proven mathematical patterns from our categorical model, ensuring that only mathematically sound and atomic operations proceed to execution.

## What the Validator Does

The Validator does NOT compile a Domain Specific Language. Instead, it:

1. **Compiles TO** the existing mathematical DSL defined in `maths/DSL/Syntax.lean`
2. **Validates** opportunities against pre-proven mathematical patterns
3. **Verifies** all constraints and safety properties are satisfied
4. **Generates** execution bundles with mathematical guarantees

## Architecture

```
Opportunity JSON → Compiler → Analyzer → Bundle Generator → Validated Bundle JSON
                      ↓          ↓              ↓
                  JSON→DSL    Pattern      Generate
                           Matching &    Execution Plan
                           Verification
```

## Three-Module Design

### 1. Compiler Module (`compiler/`)

**Purpose**: Compiles opportunity JSON into the mathematical DSL

**What it does**:
- Parses and validates incoming JSON
- Maps JSON actions to DSL Actions (e.g., "borrow" → `Action.borrow`)
- Constructs DSL Expressions using proper composition (`Expr.seq`, `Expr.parallel`)
- Infers missing information (chains, protocols)
- Creates Bundle structures with constraints

**Input**: Opportunity JSON from detection system  
**Output**: DSL Expression following `maths/DSL/Syntax.lean`

### 2. Analyzer Module (`analyzer/`)

**Purpose**: Pattern matches DSL expressions against pre-proven patterns and verifies all mathematical constraints

**What it does**:
- Maintains a library of mathematically proven patterns
- Performs structural pattern matching on DSL expressions
- Identifies which pattern (if any) matches the opportunity
- Extracts pattern parameters for instantiation
- Verifies theorem preconditions are satisfied
- Validates all constraints (deadline, gas, balance, invariants)
- Ensures atomicity and other safety properties
- Provides risk assessment and confidence scoring

**Input**: DSL Expression from Compiler  
**Output**: Analysis Result with pattern match and verification status

### 3. Bundle Generator Module (`bundle-generator/`)

**Purpose**: Transforms verified patterns into executable bundles

**What it does**:
- Takes validated patterns with their parameters
- Resolves contract addresses for all protocols
- Encodes parameters for smart contract calls
- Calculates dynamic values (e.g., swap outputs)
- Estimates gas with safety buffers
- Optimizes execution ordering
- Generates fallback options

**Input**: Analysis Result from Analyzer  
**Output**: Execution Bundle JSON ready for on-chain execution

## Mathematical Foundation

The Validator leverages the mathematical model defined in `maths/`:

- **Categorical Model**: Blockchains as a bicategory with atomic operations as 2-cells
- **Pre-proven Patterns**: General theorems proven in Lean 4 for pattern classes
- **No Runtime Proving**: We only verify that opportunities match proven patterns
- **Formal Guarantees**: Every validated bundle has a mathematical proof of atomicity

Example pattern (proven in Lean):
```lean
theorem FlashLoanPattern :
  ∀ (amount : ℚ) (token : Token) (protocol : Protocol) (middle_ops : List Op),
  amount > 0 →
  ValuePreserving middle_ops →
  IsAtomic (borrow amount token protocol ≫ middle_ops ≫ repay amount token protocol)
```

At runtime, we simply:
1. Identify this is a flash loan pattern
2. Check preconditions (amount > 0, operations preserve value)
3. Therefore the bundle is atomic (by the theorem)

## Usage

### Complete Pipeline
```bash
# Validate an opportunity through the full pipeline
./pipeline/validate < opportunity.json > validated-bundle.json
```

### Individual Modules (for testing/debugging)
```bash
# Run each module separately
echo $OPPORTUNITY_JSON | ./compiler/bin/compile > dsl.json
echo $DSL_JSON | ./analyzer/bin/analyze > pattern.json
echo $PATTERN_JSON | ./proof-verifier/bin/verify > verified.json
echo $VERIFIED_JSON | ./bundle-generator/bin/generate > bundle.json
```

## Performance Requirements

- **Compiler**: < 2ms (JSON to DSL transformation)
- **Analyzer**: < 5ms (pattern matching)
- **Proof Verifier**: < 10ms (constraint validation)
- **Bundle Generator**: < 3ms (bundle generation)
- **Total Pipeline**: < 20ms for 95% of opportunities

## Integration Points

### Input from Detection System
- Receives opportunity JSON via stdin or message queue
- Expected format defined in `shared/schemas/opportunity.json`

### Output to Execution Tools
- Outputs validated bundle JSON
- Format defined in `shared/schemas/bundle.json`
- Only mathematically verified bundles proceed

### Feedback to Detection System
- Pattern not found → helps detection learn new patterns
- Validation failures → helps tune opportunity detection
- Success metrics → reinforces good patterns

## Directory Structure

```
validator/
├── compiler/               # JSON → DSL compilation
│   ├── src/
│   ├── test/
│   └── bin/
├── analyzer/              # Pattern matching
│   ├── src/
│   ├── pattern-library/  # Pre-proven patterns
│   ├── test/
│   └── bin/
├── proof-verifier/        # Constraint validation
│   ├── src/
│   ├── test/
│   └── bin/
├── bundle-generator/      # Bundle generation
│   ├── src/
│   ├── test/
│   └── bin/
├── pipeline/             # Main pipeline script
│   └── validate
├── feedback/             # Feedback mechanisms
└── README.md            # This file
```

## Development Guidelines

1. **Modularity**: Each module should remain independent with clear interfaces
2. **Testability**: Every module must have comprehensive unit tests
3. **Performance**: Monitor and optimize for sub-20ms total latency
4. **Extensibility**: New patterns should be easy to add after Lean proofs
5. **Debugging**: Clear error messages and logging at each stage

## Adding New Patterns

1. Prove the pattern in Lean 4 (`maths/DSL/Patterns/`)
2. Export the pattern to the Analyzer's pattern library
3. Add pattern matching logic in the Analyzer
4. Add specific constraints in the Proof Verifier
5. Update Bundle Generator for any new operations

## Dependencies

- Mathematical model in `maths/` (Lean 4)
- Shared schemas and interfaces
- Real-time chain state (for feasibility checks)
- Gas price oracles
- Bridge availability APIs