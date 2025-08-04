# Analyzer Module

## Overview

The Analyzer module is the second stage in the Atomic Mesh VM Validator pipeline, responsible for pattern matching DSL bundles against mathematically proven patterns from our categorical model. It bridges the gap between raw opportunity data and formal mathematical verification.

## Project Structure

```
analyzer/
├── src/
│   ├── common/          # Shared types and analysis results
│   ├── pattern_scanner/ # Lean theorem parsing
│   ├── pattern_compiler/# Pattern to automata compilation
│   ├── matching/        # Structural pattern matching
│   ├── validation/      # Constraint validation
│   ├── semantic/        # Mathematical theorem application
│   ├── scoring/         # Confidence and risk scoring
│   ├── hotreload/       # Dynamic pattern updates
│   ├── discovery/       # Pattern discovery system
│   ├── fallback/        # Error handling & graceful degradation
│   ├── heuristics/      # Heuristic analysis for unknown patterns
│   ├── engine/          # Main analyzer engine
│   └── lib.rs          # Library exports
├── tests/
│   ├── phase2_integration.rs       # Phase 2 integration tests
│   ├── phase4_simple.rs            # Phase 4 simple tests
│   └── phase4_integration_simple.rs # Phase 4 integration tests
├── Cargo.toml
├── BUILD_PLAN.md       # Detailed implementation plan
└── README.md          # This file
```

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

5. **Semantic Validator** (`src/semantic/`)
   - `theorem_engine.rs`: Applies mathematical theorems to validate bundles
   - `proof_application.rs`: Bridges pattern matches to theorem proofs
   - Verifies atomicity, invariants, and composition laws from `maths/` folder

6. **Scoring System** (`src/scoring/`)
   - `confidence_calculator.rs`: Mathematical confidence scoring (0.0-1.0)
   - `risk_assessor.rs`: Risk assessment for unknown patterns
   - Provides graduated confidence based on proof strength

7. **Hot-Reload System** (`src/hotreload/`)
   - `filesystem_watcher.rs`: Monitors `maths/` directory for theorem changes
   - `event_handler.rs`: Processes file events and triggers recompilation
   - Enables dynamic pattern updates without system restart

8. **Pattern Discovery** (`src/discovery/`)
   - `pattern_composer.rs`: Discovers composite patterns from successful matches
   - `structure_analyzer.rs`: Analyzes bundle structures for common motifs
   - Automatically extends pattern library based on usage

9. **Fallback System** (`src/fallback/`) *[NEW in Phase 4]*
   - `analysis_result.rs`: Enhanced result types with tiered fallback
   - `result_builder.rs`: Builder pattern for constructing complex analysis results
   - Implements graceful degradation: FullMatch → PartialMatch → Heuristic → Reject

10. **Heuristic Analysis** (`src/heuristics/`) *[NEW in Phase 4]*
    - `structural_analyzer.rs`: Analyzes bundle structure without formal proofs
    - `safety_heuristics.rs`: Assesses safety properties through heuristics
    - Provides best-effort analysis when mathematical proofs unavailable

### Data Flow

```
DSL Bundle (JSON) → Tokenization → Automata Matching → Constraint Validation → Semantic Validation → Analysis Result
                                          ↓                                           ↓
                                   Pattern Library ←────────────────────┐    Theorem Application
                                   (Lean Theorems)                      │    (Mathematical Proofs)
                                          ↑                             │             ↓
                                    Hot-Reload ←──── File Changes       │    Confidence Scoring
                                          ↑                             │    Risk Assessment
                                 Pattern Discovery ←────────────────────┘             ↓
                                 (Composite Patterns)                         Heuristic Analysis
                                                                             (Fallback System)
```

### Key Types

- **ProvenPattern**: Runtime representation of a Lean theorem
- **PatternCandidate**: A potential match with confidence score
- **AnalysisResult**: Tiered result (FullMatch, PartialMatch, Heuristic, Reject)
- **FiniteAutomaton**: State machine for pattern recognition
- **RejectionReason**: Detailed error types with contextual information
- **SuggestedFix**: Actionable recommendations for invalid bundles

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

### 📊 Overall Progress: 67% Complete (4 of 6 phases)

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

### Phase 3: Extensibility & Hot-Reload System ✅ COMPLETE

**Status**: Dynamic pattern system fully operational

#### Completed Components:
- ✅ **3.1 Hot-Reload Architecture**
  - Filesystem watcher for monitoring Lean theorem files
  - Event handler for processing file change events
  - Hot-reload manager for dynamic pattern updates
  
- ✅ **3.2 Pattern Discovery System**
  - Pattern composer for discovering composite patterns
  - Structure analyzer for analyzing bundle patterns
  - Automatic pattern library extension

### Phase 4: Error Handling & Graceful Degradation ✅ COMPLETE

**Status**: Comprehensive error handling and fallback system fully implemented

#### Completed Components:
- ✅ **4.1 Tiered Fallback System**
  - Enhanced `AnalysisResult` enum with four tiers
  - `ResultBuilder` for flexible result construction
  - Graceful degradation from mathematical proofs to heuristics
  
- ✅ **4.2 Heuristic Analysis Engine**
  - Structural analyzer for pattern-less bundle analysis
  - Safety heuristics for risk assessment without proofs
  - Balance flow analysis, timing risk assessment, protocol risk scoring
  
- ✅ **4.3 Error Handling & Recovery**
  - Comprehensive `RejectionReason` types with detailed context
  - `SuggestedFix` generation for common issues
  - Risk assessment and mitigation strategies
  
- ✅ **4.4 Analyzer Engine Integration**
  - Fully integrated fallback system into main engine
  - Seamless progression through analysis tiers
  - Maintains backward compatibility with existing interfaces

### 🧪 Test Status

- **Total Tests**: 35 unit tests + 9 integration tests  
- **Pass Rate**: 100% ✅ (All 44 tests passing)
- **Build Status**: Success (minimal warnings, both debug & release)
- **Binary**: Executable runs successfully
- **Coverage**: All major components tested
- **Performance**: O(1) pattern matching achieved
- **Phase 1**: 9 pattern matching tests ✅
- **Phase 2**: 11 semantic validation tests + 3 integration tests ✅
- **Phase 3**: 9 hot-reload and discovery tests ✅
- **Phase 4**: 7 new tests + 3 integration tests ✅

### 📈 Recent Progress

- **Phase 4 Implementation** (December 2024):
  - Implemented tiered `AnalysisResult` with four distinct levels
  - Created `ResultBuilder` for complex result construction
  - Built `StructuralAnalyzer` for extracting bundle features without proofs
  - Added `SafetyHeuristics` for safety property assessment
  - Integrated fallback system into main analyzer engine
  - Fixed all compilation errors and warnings
  - All 44 tests passing (100% pass rate)

### Upcoming Phases:

- **Phase 5**: Performance Optimization & Production Readiness (Next)
- **Phase 6**: Integration & Testing

## Features

### ✅ Implemented
- **Pattern Recognition**: Finite automata-based matching with O(1) performance
- **Mathematical Verification**: Theorem application from Lean proofs
- **Tiered Analysis**: FullMatch → PartialMatch → Heuristic → Reject
- **Dynamic Patterns**: Hot-reload system for live theorem updates
- **Pattern Discovery**: Automatic composite pattern generation
- **Risk Assessment**: Comprehensive risk profiling for unknown patterns
- **Confidence Scoring**: Graduated confidence levels (0.0-1.0)
- **Error Recovery**: Graceful degradation with detailed diagnostics
- **Heuristic Analysis**: Best-effort analysis when proofs unavailable
- **Suggested Fixes**: Actionable recommendations for invalid bundles

### 🚧 Coming Soon
- **Performance Monitoring**: Sub-microsecond timing enforcement
- **Production Metrics**: Comprehensive observability
- **Pipeline Integration**: Seamless compiler → analyzer → proof verifier flow

## Usage

```bash
# Run all tests
cargo test

# Run specific test suite
cargo test --test phase4_simple

# Build the library
cargo build --lib

# Build release version
cargo build --release

# Run with sample input
echo '{"bundle": {...}}' | cargo run --bin analyzer
```

## Dependencies

- `serde`: JSON serialization
- `regex`: Pattern matching in Lean files
- `parking_lot`: High-performance synchronization
- `thiserror`: Error handling
- `num-traits`: Numeric operations for heuristics
- `common`: Shared types with compiler module

## Development

See `BUILD_PLAN.md` for detailed implementation roadmap and progress tracking.