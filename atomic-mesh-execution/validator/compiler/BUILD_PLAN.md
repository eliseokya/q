# Compiler Module Implementation Plan

This document outlines the plan to build the compiler module for the Atomic Mesh VM Validator.

## Scope

The compiler is one of four modules in the validator pipeline:
1. **Compiler** (this module) - Transforms opportunity JSON to DSL Bundle
2. Analyzer - Pattern matches against mathematical theorems
3. Proof Verifier - Verifies mathematical proofs
4. Bundle Generator - Generates executable bundles

This plan focuses ONLY on the compiler module, which must:
- Accept opportunity JSON via stdin
- Output DSL Bundle JSON via stdout
- Complete in <1.5ms
- Integrate seamlessly with the validator pipeline

## Phase 1: Core Transformation (Week 1-2) ✅ COMPLETED
**Goal**: Implement the 4-component pipeline that correctly transforms inputs

### 1.1 Complete parse-and-validate ✅ COMPLETED
- [x] JSON parsing with error reporting to stderr
- [x] Validate required fields (opportunity_id, path array)
- [x] Extract metadata, actions, and constraints
- [x] Output normalized JSON to stdout
- **Tests**: 
  - Valid opportunity structures
  - Invalid JSON handling
  - Missing field detection
  - Edge cases (empty paths, null values)

**Implementation Details**:
- Comprehensive JSON parsing with detailed error previews
- Full structure validation for all action types
- Metadata extraction with type handling (string/number)
- Constraint extraction with proper defaults
- 15+ unit tests covering all scenarios

### 1.2 Complete transform-actions ✅ COMPLETED
- [x] Convert string amounts to rational numbers {num, den}
- [x] Map token strings to DSL Token enum
- [x] Map protocol strings to DSL Protocol enum
- [x] Infer chain context from action sequence
- **Tests**:
  - Rational number conversion accuracy
  - Token/protocol mapping coverage
  - Chain inference logic
  - Error handling for unknown values

**Implementation Details**:
- Robust amount normalization (decimals, scientific notation, edge cases)
- Complete token/protocol/chain mapping with aliases
- Chain inference with round-trip validation
- Comprehensive error messages with suggestions
- 25+ unit tests including edge cases

### 1.3 Complete build-expression ✅ COMPLETED
- [x] Analyze action dependencies
- [x] Detect parallel execution opportunities
- [x] Build DSL expression tree (Seq, Parallel, OnChain)
- [x] Apply chain context wrappers
- **Tests**:
  - Sequential expression building
  - Parallel detection correctness
  - Chain wrapper placement
  - Complex expression trees

**Implementation Details**:
- Sophisticated parallel analysis with dependency detection
- Expression tree building with proper Seq/Parallel composition
- Chain context wrapping (OnChain)
- Expression optimization (flattening, simplification)
- 20+ unit tests covering all scenarios

### 1.4 Complete assemble-bundle ✅ COMPLETED
- [x] Create Bundle structure matching DSL
- [x] Map constraints to DSL Constraint types
- [x] Set bundle name and start chain
- [x] Output final JSON to stdout
- **Tests**:
  - Bundle structure validation
  - Constraint mapping
  - Complete bundle generation
  - JSON serialization

**Implementation Details**:
- Bundle name generation from opportunity ID
- Start chain determination (metadata > first action > default)
- Comprehensive constraint extraction and mapping
- Support for all constraint types (deadline, gas, balance, invariants)
- 15+ unit tests covering all cases

## Phase 2: DSL Compliance (Week 3)
**Goal**: Ensure perfect alignment with mathematical DSL

### 2.1 Mathematical Model Validation
- [ ] Validate output against maths/DSL/Syntax.lean
- [ ] Ensure all action types are supported
- [ ] Verify expression composition rules
- [ ] Check constraint completeness
- **Tests**:
  - Compare with Lean DSL examples
  - Round-trip validation
  - Type checking against DSL

### 2.2 Edge Case Handling
- [ ] Handle all valid action combinations
- [ ] Support custom tokens/protocols
- [ ] Process complex nested expressions
- [ ] Manage chain transitions correctly
- **Tests**:
  - Comprehensive action coverage
  - Custom token handling
  - Deep nesting scenarios
  - Multi-chain sequences

## Phase 3: Pipeline Integration (Week 4)
**Goal**: Seamless integration within validator pipeline

### 3.1 Unix Pipeline Compliance
- [ ] Stdin/stdout/stderr handling
- [ ] Exit codes for different error types
- [ ] JSON streaming for large inputs
- [ ] Component composability
- **Tests**:
  - Pipeline integration tests
  - Error propagation
  - Stream handling
  - Exit code validation

### 3.2 Inter-component Communication
- [ ] Standardized JSON formats between components
- [ ] Error format consistency
- [ ] Metadata preservation through pipeline
- [ ] Performance within pipeline context
- **Tests**:
  - Full pipeline execution
  - Data flow validation
  - Error handling across components
  - End-to-end performance

## Phase 4: Performance Optimization (Week 5)
**Goal**: Meet <1.5ms compilation target

### 4.1 Component Performance
- [ ] parse-and-validate: <0.3ms
- [ ] transform-actions: <0.4ms
- [ ] build-expression: <0.6ms
- [ ] assemble-bundle: <0.2ms
- **Tests**:
  - Component benchmarks
  - Memory usage profiling
  - CPU profiling
  - Optimization validation

### 4.2 Pipeline Optimization
- [ ] Minimize allocations
- [ ] Optimize JSON parsing/serialization
- [ ] Efficient data structures
- [ ] Fast rational arithmetic
- **Tests**:
  - End-to-end latency
  - Throughput testing
  - Resource usage
  - Performance regression tests

## Phase 5: Robustness (Week 6)
**Goal**: Production-ready reliability

### 5.1 Error Handling
- [ ] Comprehensive error messages
- [ ] Helpful error suggestions
- [ ] Graceful degradation
- [ ] Input validation
- **Tests**:
  - Error message quality
  - Edge case handling
  - Malformed input handling
  - Recovery scenarios

### 5.2 Testing Coverage
- [ ] 90%+ code coverage
- [ ] Property-based tests
- [ ] Fuzz testing
- [ ] Integration test suite
- **Tests**:
  - Coverage metrics
  - Test quality assessment
  - Mutation testing
  - Real-world scenarios

## Testing Strategy

### Unit Tests
- Each component: 50+ tests
- Each module (parser, transformer, etc.): 20+ tests
- Focus on correctness and edge cases

### Integration Tests
- Component interaction
- Pipeline flow
- Error propagation
- Performance benchmarks

### Validation Tests
- DSL compliance
- Mathematical correctness
- Output format validation
- Constraint handling

## Success Criteria

1. **Correctness**: 100% valid transformations match DSL spec
2. **Performance**: <1.5ms compilation (p99)
3. **Reliability**: No crashes on valid input
4. **Integration**: Seamless pipeline operation
5. **Maintainability**: Clear code, comprehensive tests

## Deliverables

1. **Four executable binaries** in `bin/`:
   - parse-and-validate
   - transform-actions
   - build-expression
   - assemble-bundle

2. **Pipeline script**: `pipeline.sh`

3. **Test suite** with fixtures

4. **Documentation** for integration

## Implementation Guidelines

### Technical Constraints
- Rust implementation
- No external dependencies beyond std/serde
- Unix philosophy adherence
- JSON communication only
- Deterministic output

### Quality Standards
- Clean, idiomatic Rust
- Comprehensive error handling
- Performance-conscious design
- Well-documented code
- Extensive test coverage

## Timeline Summary

- **Weeks 1-2**: Core transformation complete ✅
- **Week 3**: DSL compliance verified
- **Week 4**: Pipeline integration working
- **Week 5**: Performance targets met
- **Week 6**: Production robustness achieved

Total: 6 weeks to production-ready compiler module

## Out of Scope

The following are explicitly NOT part of this compiler module:
- gRPC/REST APIs (handled by execution engine)
- WebAssembly compilation
- External language bindings
- Monitoring/metrics (handled by execution engine)
- Database integration
- Network communication
- Smart contract generation (handled by bundle generator)
- Proof verification (handled by proof verifier)
- Pattern matching (handled by analyzer)

This module is strictly a transformation component in the validator pipeline.