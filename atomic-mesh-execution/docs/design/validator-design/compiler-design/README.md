# Compiler Design Documentation

This directory contains the comprehensive design documentation for the Compiler module of the Atomic Mesh VM Validator.

## Overview

The Compiler transforms opportunity JSON from the detection system into the mathematical DSL Bundle format defined in `maths/DSL/Syntax.lean`. It implements a 4-component pipeline that balances Unix philosophy with practical performance requirements.

## Design Documents

### Architecture & Design
- `architecture.md` - 4-component architecture and design principles
- `design-summary.md` - Executive summary of design decisions and rationale
- `data-flow.md` - Data transformations at each pipeline stage
- `output-format.md` - DSL Bundle JSON output specification

### Implementation Details
- `pipeline-specification.md` - Pipeline execution and component interfaces
- `mapping-rules.md` - Exact transformation rules for all data types
- `performance-optimization.md` - Optimization strategies and benchmarks
- `testing-strategy.md` - Comprehensive testing approach

## Key Design Decisions

1. **4-Component Pipeline**: Optimal balance of modularity and performance
2. **JSON Communication**: Debuggable text streams between components
3. **Rational Numbers**: Exact arithmetic matching mathematical model
4. **Parallel Detection**: Identifies optimization opportunities
5. **Type Progressive**: Gradual transformation to typed representation

## Pipeline Overview

```
Opportunity JSON 
    ↓
parse-and-validate (0.3ms)
    ↓
transform-actions (0.4ms)
    ↓
build-expression (0.6ms)
    ↓
assemble-bundle (0.2ms)
    ↓
DSL Bundle JSON (Total: < 1.5ms)
```

## Quick Start

1. Read `design-summary.md` for executive overview
2. Review `architecture.md` for component details
3. Check `mapping-rules.md` for transformation specifications
4. See `testing-strategy.md` for quality assurance approach

## Implementation Status

✅ Design Phase Complete
⏳ Implementation Phase Starting

The design provides a solid foundation for building a high-performance compiler that maintains mathematical correctness while meeting strict latency requirements.