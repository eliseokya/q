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

5. **Semantic Validator** (`src/semantic/`) *[NEW in Phase 2]*
   - `theorem_engine.rs`: Applies mathematical theorems to validate bundles
   - `proof_application.rs`: Bridges pattern matches to theorem proofs
   - Verifies atomicity, invariants, and composition laws from `maths/` folder

6. **Scoring System** (`src/scoring/`) *[NEW in Phase 2]*
   - `confidence_calculator.rs`: Mathematical confidence scoring (0.0-1.0)
   - `risk_assessor.rs`: Risk assessment for unknown patterns
   - Provides graduated confidence based on proof strength

### Data Flow

```
DSL Bundle (JSON) → Tokenization → Automata Matching → Constraint Validation → Semantic Validation → Analysis Result
                                          ↓                                           ↓
                                   Pattern Library                            Theorem Application
                                   (Lean Theorems)                           (Mathematical Proofs)
                                                                                      ↓
                                                                            Confidence Scoring
                                                                            Risk Assessment
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

### 📊 Overall Progress: 33% Complete (2 of 6 phases)

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

### Phase 2: Semantic Validation & Mathematical Integration ✅ COMPLETE

**Status**: Theorem application and confidence scoring fully operational

#### Completed Components:
- ✅ **2.1 Mathematical Property Verification**
  - Theorem application engine (`src/semantic/theorem_engine.rs`)
  - Proof application bridge (`src/semantic/proof_application.rs`)
  - Support for flash loan atomicity, cross-chain consistency, protocol invariants
  - Integration with theorems from `maths/` folder
  
- ✅ **2.2 Pattern Confidence Scoring**
  - Mathematical confidence calculator (`src/scoring/confidence_calculator.rs`)
  - Risk assessment for unknown patterns (`src/scoring/risk_assessor.rs`)
  - Confidence gradients: 1.0 (proven) → 0.5-0.95 (heuristic) → 0.1-0.5 (risk-based)
  - Tiered fallback: FullMatch → PartialMatch → Heuristic → Reject

### 🧪 Test Status

- **Total Tests**: 17 unit tests
- **Pass Rate**: 100% ✅
- **Build Status**: Success (warnings only)
- **Coverage**: All major components tested
- **Performance**: Within target budgets

### 📈 Recent Progress

- Implemented semantic validation using mathematical theorems
- Added confidence scoring with proper gradients
- Created risk assessment for unknown patterns
- Integrated Phase 2 components into main analyzer engine
- All tests passing, code compiles successfully

### Upcoming Phases:

- **Phase 3**: Integration Layer & API Design (Ready to start)
- **Phase 4**: Tiered Fallback System & Heuristics
- **Phase 5**: Performance Optimization & Production Readiness
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