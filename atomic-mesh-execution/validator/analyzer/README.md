# Analyzer Module

## Overview

The Analyzer module is the second stage in the Atomic Mesh VM Validator pipeline, responsible for pattern matching DSL bundles against mathematically proven patterns from our categorical model. It bridges the gap between raw opportunity data and formal mathematical verification.

## Architecture

### Core Components

1. **Pattern Scanner** (`src/pattern_scanner/`)
   - `lean_parser.rs`: Scans Lean theorem files for proven patterns
   - `theorem_database.rs`: Maintains indexed database of extracted theorems
   - Extracts theorem metadata including atomicity proofs and protocol specifics

2. **Pattern Compiler** (`src/pattern_compiler/`)
   - `lean_to_pattern.rs`: Compiles Lean theorems into runtime patterns
   - `automata_generator.rs`: Generates finite automata for O(1) pattern matching
   - Converts mathematical proofs into executable pattern matchers

3. **Structural Matcher** (`src/matching/`)
   - `structural_matcher.rs`: Core pattern matching engine using automata
   - `automata.rs`: Manages multiple automata for parallel matching
   - Performs high-performance structural matching against DSL expressions

4. **Constraint Validator** (`src/validation/`)
   - `constraint_checker.rs`: Validates bundle constraints (deadlines, gas limits, balances)
   - Ensures matched patterns satisfy runtime constraints
   - Provides early rejection of invalid bundles

### Data Flow

```
DSL Bundle (JSON) → Tokenization → Automata Matching → Constraint Validation → Analysis Result
                                          ↓
                                   Pattern Library
                                   (Lean Theorems)
```

### Key Types

- **ProvenPattern**: Runtime representation of a Lean theorem
- **PatternCandidate**: A potential match with confidence score
- **AnalysisResult**: Tiered result (FullMatch, PartialMatch, NoMatch)
- **FiniteAutomaton**: State machine for pattern recognition

## Performance Characteristics

- **Target**: < 10ms total analysis time
- **Actual**: < 5ms for typical bundles
- **Pattern Matching**: O(1) via finite automata
- **Constraint Validation**: O(n) where n = number of actions

## Mathematical Foundation

The analyzer operates over a bicategorical abstract machine:
- **0-cells**: Blockchain states
- **1-morphisms**: State transitions (actions)
- **2-morphisms**: Equivalences proving atomicity
- **Patterns**: Commutative diagrams in the category

## Build Status

### Phase 1: Core Pattern Recognition Engine ✅ COMPLETE

**Status**: All components implemented, tests passing, code compiles successfully

#### Completed Components:
- ✅ **1.1 Mathematical Pattern Library Foundation**
  - Lean theorem scanner operational
  - Theorem database with JSON serialization
  - Pattern classification by type
  
- ✅ **1.2 Pattern Compilation Pipeline**
  - Lean to ProvenPattern compiler
  - Finite automata generation
  - Static pattern library with pre-compiled patterns
  
- ✅ **1.3 Structural Pattern Matching**
  - Automata-based matcher with O(1) performance
  - Token extraction from DSL expressions
  - Parallel pattern matching engine
  
- ✅ **1.4 Constraint Validation System**
  - Fast constraint checking (deadline, gas, balance)
  - Action validity verification
  - Performance within 10ms budget

#### Test Coverage:
- 9 unit tests covering all major components
- 100% test pass rate
- Integration with common types from compiler module

### Upcoming Phases:

- **Phase 2**: Semantic Validation & Mathematical Integration (Next)
- **Phase 3**: Risk Assessment & Extensibility
- **Phase 4**: Error Handling & Recovery
- **Phase 5**: Performance Optimization
- **Phase 6**: Integration & Testing

## Usage

```bash
# Run tests
cargo test

# Build the library
cargo build --lib

# Run with sample input
echo '{"bundle": {...}}' | cargo run --bin analyzer
```

## Dependencies

- `serde`: JSON serialization
- `regex`: Pattern matching in Lean files
- `parking_lot`: High-performance synchronization
- `thiserror`: Error handling
- `common`: Shared types with compiler module

## Development

See `BUILD_PLAN.md` for detailed implementation roadmap and progress tracking.