# Compiler Performance Optimization

## Overview

The compiler must meet strict performance requirements (< 1.5ms total) to support high-frequency execution. This document details optimization strategies for each component.

## Performance Targets

| Component | Target | Critical Path | Optimization Priority |
|-----------|--------|---------------|---------------------|
| parse-and-validate | < 0.3ms | Yes | High |
| transform-actions | < 0.4ms | Yes | Critical |
| build-expression | < 0.6ms | Yes | Medium |
| assemble-bundle | < 0.2ms | Yes | Low |
| **Total** | **< 1.5ms** | - | - |

## Component-Specific Optimizations

### parse-and-validate

**Bottlenecks**:
- JSON parsing
- Field validation
- Memory allocation

**Optimizations**:
1. **Streaming JSON Parser**: Use `serde_json`'s streaming API
   ```rust
   let mut deserializer = serde_json::Deserializer::from_reader(stdin);
   let value = Value::deserialize(&mut deserializer)?;
   ```

2. **Pre-allocated Buffers**: Reuse buffers for common sizes
   ```rust
   const TYPICAL_SIZE: usize = 2048;
   let mut buffer = Vec::with_capacity(TYPICAL_SIZE);
   ```

3. **Fast Path for Common Cases**: Special handling for typical patterns
   ```rust
   // Fast path for standard 3-5 action sequences
   if path.len() >= 3 && path.len() <= 5 {
       // Optimized validation
   }
   ```

4. **Lazy Validation**: Validate only what's needed
   ```rust
   // Don't validate unused fields
   if !has_constraints {
       skip_constraint_validation();
   }
   ```

### transform-actions

**Bottlenecks**:
- String to rational conversion
- Token/protocol mapping
- Chain inference

**Optimizations**:
1. **Lookup Tables**: Pre-computed hash maps for mappings
   ```rust
   lazy_static! {
       static ref TOKEN_MAP: HashMap<&'static str, Token> = {
           let mut m = HashMap::new();
           m.insert("eth", Token::ETH);
           m.insert("weth", Token::WETH);
           // ... more mappings
           m
       };
   }
   ```

2. **Optimized Rational Conversion**: Fast path for integers
   ```rust
   fn parse_amount(s: &str) -> Result<Rational> {
       // Fast path for integers
       if let Ok(n) = s.parse::<u64>() {
           return Ok(Rational { num: n, den: 1 });
       }
       // Slower path for decimals
       parse_decimal(s)
   }
   ```

3. **Chain Context Caching**: Avoid repeated lookups
   ```rust
   struct ChainTracker {
       current: Chain,
       cache: Vec<(usize, Chain)>, // (action_index, chain)
   }
   ```

4. **Batch Processing**: Process multiple fields together
   ```rust
   // Process all token mappings in one pass
   actions.par_iter_mut().for_each(|action| {
       action.token = TOKEN_MAP[&action.token.to_lowercase()];
   });
   ```

### build-expression

**Bottlenecks**:
- Parallel detection algorithm
- Tree construction
- Memory allocation for nested structures

**Optimizations**:
1. **Dependency Graph**: Pre-compute action dependencies
   ```rust
   struct DependencyGraph {
       edges: Vec<(usize, usize)>, // (from_idx, to_idx)
       independent_groups: Vec<Vec<usize>>,
   }
   ```

2. **Expression Pool**: Reuse expression nodes
   ```rust
   struct ExprPool {
       seq_nodes: Vec<SeqExpr>,
       action_nodes: Vec<ActionExpr>,
       // Reuse allocated nodes
   }
   ```

3. **Iterative Tree Building**: Avoid recursion overhead
   ```rust
   fn build_expression_iterative(actions: &[Action]) -> Expr {
       let mut stack = Vec::with_capacity(actions.len());
       // Build tree iteratively
   }
   ```

4. **Parallel Detection Heuristics**: Fast approximate detection
   ```rust
   // Quick check for obvious parallel opportunities
   fn can_parallelize_fast(a1: &Action, a2: &Action) -> bool {
       a1.chain != a2.chain && !shares_tokens(a1, a2)
   }
   ```

### assemble-bundle

**Bottlenecks**:
- JSON serialization
- String allocation

**Optimizations**:
1. **Pre-sized Output Buffer**: Estimate output size
   ```rust
   let estimated_size = estimate_bundle_size(&expr, &constraints);
   let mut output = String::with_capacity(estimated_size);
   ```

2. **Direct Serialization**: Write directly to output
   ```rust
   use std::io::Write;
   let stdout = std::io::stdout();
   let mut handle = stdout.lock();
   serde_json::to_writer(&mut handle, &bundle)?;
   ```

3. **Minimal Copying**: Use references where possible
   ```rust
   #[derive(Serialize)]
   struct BundleRef<'a> {
       name: &'a str,
       #[serde(rename = "startChain")]
       start_chain: &'a str,
       // Use references to avoid copying
   }
   ```

## Cross-Component Optimizations

### Memory Management

1. **Arena Allocation**: Use arena allocator for temporary objects
   ```rust
   use typed_arena::Arena;
   let arena = Arena::new();
   // Allocate all temporary objects in arena
   ```

2. **Zero-Copy Parsing**: Parse directly from input buffer
   ```rust
   // Use serde's zero-copy deserialization
   #[derive(Deserialize)]
   struct Action<'a> {
       #[serde(borrow)]
       action: &'a str,
       // Borrow strings instead of allocating
   }
   ```

### Pipeline Optimizations

1. **Buffer Pooling**: Share buffers between components
   ```rust
   // Thread-local buffer pool
   thread_local! {
       static BUFFER_POOL: RefCell<Vec<Vec<u8>>> = RefCell::new(vec![]);
   }
   ```

2. **Minimal Serialization**: Use compact intermediate format
   ```rust
   // Instead of full JSON between components, use MessagePack
   use rmp_serde::{Deserializer, Serializer};
   ```

## Profiling and Benchmarking

### Micro-benchmarks

Create benchmarks for each critical function:
```rust
#[bench]
fn bench_parse_amount(b: &mut Bencher) {
    b.iter(|| {
        parse_amount("123.456")
    });
}

#[bench]
fn bench_token_mapping(b: &mut Bencher) {
    b.iter(|| {
        map_token("weth")
    });
}
```

### Component Benchmarks

Test full component performance:
```rust
#[bench]
fn bench_transform_actions_typical(b: &mut Bencher) {
    let input = load_typical_input();
    b.iter(|| {
        transform_actions(&input)
    });
}
```

### Pipeline Benchmarks

Measure end-to-end performance:
```bash
#!/bin/bash
# benchmark.sh
echo "Warming up..."
for i in {1..100}; do
    cat typical_opportunity.json | ./pipeline.sh > /dev/null
done

echo "Benchmarking..."
time for i in {1..1000}; do
    cat typical_opportunity.json | ./pipeline.sh > /dev/null
done
```

## Common Patterns Optimization

### Flash Loan Pattern
Optimize for the common borrow → operations → repay pattern:
```rust
// Fast detection of flash loan pattern
fn is_flash_loan(actions: &[Action]) -> Option<FlashLoanInfo> {
    if actions.len() < 3 { return None; }
    
    if let (Some(borrow), Some(repay)) = (
        actions.first().and_then(as_borrow),
        actions.last().and_then(as_repay)
    ) {
        if borrow.token == repay.token && borrow.amount == repay.amount {
            return Some(FlashLoanInfo { /* ... */ });
        }
    }
    None
}
```

### Arbitrage Pattern
Optimize for swap sequences:
```rust
// Detect arbitrage cycles efficiently
fn detect_arbitrage_cycle(swaps: &[SwapAction]) -> Option<ArbitrageCycle> {
    // Use graph algorithm to find cycles
    let mut graph = TokenGraph::new();
    for swap in swaps {
        graph.add_edge(swap.token_in, swap.token_out);
    }
    graph.find_cycle()
}
```

## Memory Layout Optimizations

### Struct Packing
Optimize struct layout for cache efficiency:
```rust
// Before: 32 bytes (with padding)
struct Action {
    action_type: ActionType, // 1 byte + 7 padding
    amount: Rational,        // 16 bytes
    token: Token,           // 1 byte + 7 padding
}

// After: 24 bytes (packed)
#[repr(C)]
struct Action {
    amount: Rational,        // 16 bytes
    action_type: ActionType, // 1 byte
    token: Token,           // 1 byte
    _padding: [u8; 6],      // Explicit padding
}
```

### Enum Optimization
Use compact representations:
```rust
// Use u8 for small enums
#[repr(u8)]
enum Token {
    ETH = 0,
    WETH = 1,
    USDC = 2,
    DAI = 3,
}

// Pack multiple enums in one byte
struct PackedData {
    data: u8, // bits 0-3: token, bits 4-7: protocol
}
```

## Parallelization Opportunities

### Independent Validations
Run independent validations in parallel:
```rust
use rayon::prelude::*;

let validations = vec![
    || validate_tokens(&actions),
    || validate_protocols(&actions),
    || validate_amounts(&actions),
];

let results: Vec<_> = validations
    .par_iter()
    .map(|f| f())
    .collect();
```

### Batch Processing
Process multiple opportunities in parallel:
```rust
// Process multiple opportunities in parallel
fn process_batch(opportunities: Vec<Opportunity>) -> Vec<Bundle> {
    opportunities
        .par_iter()
        .map(|opp| compile_opportunity(opp))
        .collect()
}
```

## Monitoring and Metrics

### Performance Counters
Track key metrics:
```rust
struct Metrics {
    parse_time: Histogram,
    transform_time: Histogram,
    build_time: Histogram,
    assemble_time: Histogram,
    total_time: Histogram,
    
    cache_hits: Counter,
    cache_misses: Counter,
}
```

### Adaptive Optimization
Adjust strategies based on workload:
```rust
// Switch strategies based on input size
fn choose_strategy(input_size: usize) -> Strategy {
    match input_size {
        0..=1000 => Strategy::Simple,
        1001..=5000 => Strategy::Optimized,
        _ => Strategy::Parallel,
    }
}
```

## Future Optimizations

### JIT Compilation
For hot paths, consider JIT:
```rust
// Use cranelift for JIT compilation of hot functions
use cranelift_simplejit::{SimpleJITBuilder};
```

### SIMD Operations
Use SIMD for batch operations:
```rust
// Use packed_simd for parallel operations
use packed_simd::{u64x4};

fn sum_amounts_simd(amounts: &[u64]) -> u64 {
    // SIMD implementation
}
```

### GPU Acceleration
For massive batch processing:
```rust
// Use rust-gpu for GPU acceleration
#[spirv(compute(threads(64)))]
pub fn batch_transform_gpu(
    #[spirv(global_invocation_id)] id: UVec3,
    // GPU kernel implementation
) {
    // Parallel transformation on GPU
}
```

## Conclusion

These optimizations should enable the compiler to consistently meet the < 1.5ms target while maintaining correctness and maintainability. Regular profiling and benchmarking will ensure performance remains optimal as the system evolves.