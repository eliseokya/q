# Analyzer Module

## Purpose
The Analyzer module performs pattern matching on DSL expressions against pre-proven mathematical patterns from our categorical model.

## Functionality
- Maintains a library of mathematically proven patterns
- Performs structural pattern matching on DSL expressions
- Identifies which pattern (if any) matches the opportunity
- Extracts pattern parameters for instantiation
- References Lean proofs for matched patterns

## Input/Output
- **Input**: DSL Expression from Compiler
- **Output**: Matched Pattern with parameters and proof reference

## Performance Target
- < 5ms pattern matching time

## Directory Structure
- `src/`: Pattern matching engine
- `pattern-library/`: Pre-proven pattern definitions
- `test/`: Unit tests
- `bin/`: Compiled executable

## Pattern Library
The `pattern-library/` contains exported patterns from Lean proofs such as:
- FlashLoanPattern
- CrossChainArbPattern
- TriangularArbPattern
- And many more...