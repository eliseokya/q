# Validator Design Documentation

## Overview
This directory contains the design documents for each module in the Atomic Mesh Validator pipeline.

## Module Design Documents
- `compiler-design/` - Design documents for the compiler module
- `analyzer-design/` - Design documents for the analyzer module  
- `bundle-generator-design/` - Design documents for the bundle generator module

## Architecture
The validator consists of three sequential modules:

1. **Compiler**: Transforms opportunity JSON → Mathematical DSL
2. **Analyzer**: Pattern matches and verifies mathematical constraints
3. **Bundle Generator**: Creates executable bundles from verified patterns

See `validator_higher_level_design.md` for the complete system architecture.