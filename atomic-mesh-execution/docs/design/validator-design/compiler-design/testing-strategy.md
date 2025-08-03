# Compiler Testing Strategy

## Overview

This document defines the comprehensive testing strategy for the 4-component compiler. Testing ensures correctness, performance, and robustness across all components and the integrated pipeline.

## Testing Levels

### 1. Unit Tests
Test individual functions and modules in isolation.

### 2. Integration Tests
Test component interactions and data flow.

### 3. End-to-End Tests
Test the complete pipeline with real-world scenarios.

### 4. Performance Tests
Verify performance requirements are met.

### 5. Property-Based Tests
Use generative testing to find edge cases.

### 6. Fuzz Tests
Test with random/malformed inputs for robustness.

## Component-Specific Testing

### parse-and-validate

#### Unit Tests
```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_valid_json() {
        let input = r#"{"opportunity_id": "test", "path": []}"#;
        let result = parse_json(input);
        assert!(result.is_ok());
    }

    #[test]
    fn test_parse_malformed_json() {
        let input = r#"{"invalid": json"#;
        let result = parse_json(input);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().code, "MALFORMED_JSON");
    }

    #[test]
    fn test_validate_required_fields() {
        let input = json!({
            "path": [{"action": "borrow"}]
        });
        let result = validate_structure(&input);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().code, "MISSING_FIELD");
    }

    #[test]
    fn test_extract_metadata() {
        let input = json!({
            "opportunity_id": "test_123",
            "source_chain": "polygon",
            "extra_field": "ignored"
        });
        let metadata = extract_metadata(&input);
        assert_eq!(metadata.opportunity_id, "test_123");
        assert_eq!(metadata.source_chain, Some("polygon"));
    }
}
```

#### Integration Tests
```rust
#[test]
fn test_parse_and_validate_full() {
    let input = include_str!("../fixtures/valid_opportunity.json");
    let output = parse_and_validate(input).unwrap();
    
    assert!(output.contains("metadata"));
    assert!(output.contains("actions"));
    assert!(output.contains("constraints"));
}
```

### transform-actions

#### Unit Tests
```rust
#[test]
fn test_parse_amount_integer() {
    assert_eq!(
        parse_amount("100").unwrap(),
        Rational { num: 100, den: 1 }
    );
}

#[test]
fn test_parse_amount_decimal() {
    assert_eq!(
        parse_amount("1.5").unwrap(),
        Rational { num: 3, den: 2 }
    );
}

#[test]
fn test_map_token() {
    assert_eq!(map_token("weth").unwrap(), Token::WETH);
    assert_eq!(map_token("WETH").unwrap(), Token::WETH);
    assert!(map_token("unknown").is_err());
}

#[test]
fn test_infer_chain_context() {
    let actions = vec![
        Action { action: "borrow", chain: None },
        Action { action: "bridge", to: Some("arbitrum") },
        Action { action: "swap", chain: None },
    ];
    
    let result = infer_chains(actions, "polygon");
    assert_eq!(result[0].chain, Some("polygon"));
    assert_eq!(result[2].chain, Some("arbitrum"));
}
```

#### Property-Based Tests
```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_rational_conversion_roundtrip(n: u64, d in 1u64..=1000) {
        let rational = Rational { num: n, den: d };
        let decimal = rational.to_decimal();
        let parsed = parse_amount(&decimal).unwrap();
        
        // Should be equivalent after reduction
        assert_eq!(
            parsed.reduce(),
            rational.reduce()
        );
    }
}
```

### build-expression

#### Unit Tests
```rust
#[test]
fn test_sequential_expression() {
    let actions = vec![
        Action::borrow(100, Token::WETH, Protocol::Aave),
        Action::swap(100, Token::WETH, Token::USDC, 150000, Protocol::UniswapV2),
    ];
    
    let expr = build_sequential(&actions);
    
    match expr {
        Expr::Seq(e1, e2) => {
            assert!(matches!(e1.as_ref(), Expr::Action(_)));
            assert!(matches!(e2.as_ref(), Expr::Action(_)));
        }
        _ => panic!("Expected Seq expression"),
    }
}

#[test]
fn test_parallel_detection() {
    let actions = vec![
        Action { chain: "polygon", ..Default::default() },
        Action { chain: "arbitrum", ..Default::default() },
    ];
    
    let groups = detect_parallel_groups(&actions);
    assert_eq!(groups.len(), 2);
    assert!(can_parallelize(&actions[0], &actions[1]));
}

#[test]
fn test_onchain_wrapping() {
    let expr = Expr::Action(Action::swap(..));
    let wrapped = wrap_onchain("arbitrum", expr);
    
    match wrapped {
        Expr::OnChain { chain, expr } => {
            assert_eq!(chain, "arbitrum");
            assert!(matches!(expr.as_ref(), Expr::Action(_)));
        }
        _ => panic!("Expected OnChain expression"),
    }
}
```

### assemble-bundle

#### Unit Tests
```rust
#[test]
fn test_bundle_assembly() {
    let expr = Expr::Action(Action::borrow(..));
    let constraints = vec![Constraint::deadline(20)];
    
    let bundle = assemble_bundle("test_123", "polygon", expr, constraints);
    
    assert_eq!(bundle.name, "test_123");
    assert_eq!(bundle.start_chain, "polygon");
    assert_eq!(bundle.constraints.len(), 1);
}

#[test]
fn test_json_serialization() {
    let bundle = Bundle {
        name: "test".to_string(),
        start_chain: "polygon".to_string(),
        expr: Expr::Action(Action::borrow(..)),
        constraints: vec![],
    };
    
    let json = serde_json::to_string(&bundle).unwrap();
    assert!(json.contains(r#""type":"Bundle""#));
    assert!(json.contains(r#""name":"test""#));
}
```

## Integration Test Scenarios

### Happy Path Tests

#### Flash Loan
```rust
#[test]
fn test_flash_loan_compilation() {
    let input = r#"{
        "opportunity_id": "flash_001",
        "path": [
            {"action": "borrow", "amount": "100", "token": "WETH", "protocol": "aave"},
            {"action": "swap", "from": "WETH", "to": "USDC", "amount": "100", "minOut": "150000"},
            {"action": "repay", "amount": "100", "token": "WETH", "protocol": "aave"}
        ]
    }"#;
    
    let result = compile_opportunity(input);
    assert!(result.is_ok());
    
    let bundle = result.unwrap();
    assert_eq!(bundle.name, "flash_001");
    
    // Verify flash loan structure
    match &bundle.expr {
        Expr::Seq(borrow, Expr::Seq(swap, repay)) => {
            // Verify borrow and repay match
        }
        _ => panic!("Unexpected expression structure"),
    }
}
```

#### Cross-Chain Arbitrage
```rust
#[test]
fn test_cross_chain_arbitrage() {
    let input = include_str!("../fixtures/cross_chain_arbitrage.json");
    let bundle = compile_opportunity(input).unwrap();
    
    // Verify OnChain wrapping
    assert!(contains_onchain(&bundle.expr, "arbitrum"));
}
```

#### Parallel Operations
```rust
#[test]
fn test_parallel_operations() {
    let input = include_str!("../fixtures/parallel_swaps.json");
    let bundle = compile_opportunity(input).unwrap();
    
    // Verify parallel structure
    assert!(contains_parallel(&bundle.expr));
}
```

### Error Path Tests

#### Invalid Token
```rust
#[test]
fn test_invalid_token_error() {
    let input = r#"{
        "opportunity_id": "test",
        "path": [
            {"action": "swap", "from": "INVALID", "to": "USDC", "amount": "100"}
        ]
    }"#;
    
    let result = compile_opportunity(input);
    assert!(result.is_err());
    
    let error = result.unwrap_err();
    assert_eq!(error.code, "UNKNOWN_TOKEN");
    assert!(error.message.contains("INVALID"));
}
```

#### Chain Mismatch
```rust
#[test]
fn test_chain_mismatch_error() {
    // Test protocol not available on chain
    let input = r#"{
        "opportunity_id": "test",
        "source_chain": "polygon",
        "path": [
            {"action": "borrow", "protocol": "arbitrum-only-protocol"}
        ]
    }"#;
    
    let result = compile_opportunity(input);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().code, "CHAIN_MISMATCH");
}
```

## Performance Testing

### Benchmarks
```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn benchmark_typical_opportunity(c: &mut Criterion) {
    let input = include_str!("../fixtures/typical_opportunity.json");
    
    c.bench_function("compile typical opportunity", |b| {
        b.iter(|| compile_opportunity(black_box(input)))
    });
}

fn benchmark_complex_opportunity(c: &mut Criterion) {
    let input = include_str!("../fixtures/complex_opportunity.json");
    
    c.bench_function("compile complex opportunity", |b| {
        b.iter(|| compile_opportunity(black_box(input)))
    });
}

criterion_group!(benches, benchmark_typical_opportunity, benchmark_complex_opportunity);
criterion_main!(benches);
```

### Performance Assertions
```rust
#[test]
fn test_performance_requirements() {
    let input = include_str!("../fixtures/typical_opportunity.json");
    
    let start = std::time::Instant::now();
    let _ = compile_opportunity(input).unwrap();
    let duration = start.elapsed();
    
    assert!(duration.as_micros() < 1500, "Compilation took {:?}, exceeding 1.5ms target", duration);
}
```

## Property-Based Testing

### Action Properties
```rust
proptest! {
    #[test]
    fn test_action_properties(
        amount in 1u64..=1_000_000,
        token in prop::sample::select(vec!["ETH", "WETH", "USDC", "DAI"]),
        protocol in prop::sample::select(vec!["aave", "uniswap", "compound"])
    ) {
        let action = json!({
            "action": "borrow",
            "amount": amount.to_string(),
            "token": token,
            "protocol": protocol
        });
        
        let result = transform_action(&action);
        prop_assert!(result.is_ok());
        
        let transformed = result.unwrap();
        prop_assert_eq!(transformed.amount.num, amount);
        prop_assert_eq!(transformed.amount.den, 1);
    }
}
```

### Expression Tree Properties
```rust
proptest! {
    #[test]
    fn test_expression_tree_depth(actions in prop::collection::vec(any_action(), 1..20)) {
        let expr = build_expression(&actions);
        
        // Tree depth should be actions.len() - 1 for sequential
        let depth = calculate_depth(&expr);
        prop_assert_eq!(depth, actions.len() - 1);
        
        // All actions should be present
        let action_count = count_actions(&expr);
        prop_assert_eq!(action_count, actions.len());
    }
}
```

## Fuzz Testing

### Input Fuzzing
```rust
#[test]
fn fuzz_json_parser() {
    use arbitrary::{Arbitrary, Unstructured};
    
    let corpus = vec![
        include_bytes!("../corpus/valid1.json"),
        include_bytes!("../corpus/valid2.json"),
        // ... more seed inputs
    ];
    
    for _ in 0..10000 {
        let data = generate_fuzz_input(&corpus);
        let _ = parse_json(&data); // Should not panic
    }
}
```

### Mutation Testing
```rust
#[test]
fn test_mutated_inputs() {
    let base = include_str!("../fixtures/valid_opportunity.json");
    
    // Test with mutated versions
    for mutation in generate_mutations(base) {
        let result = compile_opportunity(&mutation);
        
        // Should either succeed or return proper error
        match result {
            Ok(_) => { /* valid mutation */ },
            Err(e) => {
                assert!(e.code.is_some());
                assert!(e.message.is_some());
            }
        }
    }
}
```

## Test Fixtures

### Directory Structure
```
test/fixtures/
├── valid/
│   ├── simple_borrow.json
│   ├── flash_loan.json
│   ├── cross_chain_arb.json
│   ├── parallel_swaps.json
│   └── complex_multi_hop.json
├── invalid/
│   ├── malformed_json.json
│   ├── missing_fields.json
│   ├── unknown_token.json
│   └── invalid_amount.json
└── performance/
    ├── typical_3_actions.json
    ├── complex_10_actions.json
    └── stress_100_actions.json
```

### Fixture Generation
```rust
// Generate test fixtures programmatically
fn generate_test_fixtures() {
    let fixtures = vec![
        ("simple_borrow", generate_simple_borrow()),
        ("flash_loan", generate_flash_loan()),
        ("parallel_ops", generate_parallel_ops()),
    ];
    
    for (name, fixture) in fixtures {
        let path = format!("test/fixtures/valid/{}.json", name);
        std::fs::write(path, serde_json::to_string_pretty(&fixture).unwrap()).unwrap();
    }
}
```

## Coverage Requirements

### Target Coverage
- Unit test coverage: > 90%
- Integration test coverage: > 80%
- Critical path coverage: 100%

### Coverage Measurement
```bash
# Run with coverage
cargo tarpaulin --out Html --output-dir coverage

# Check coverage thresholds
cargo tarpaulin --fail-under 90
```

## Continuous Integration

### CI Pipeline
```yaml
# .github/workflows/test.yml
name: Test Suite

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - uses: actions-rs/toolchain@v1
      - name: Run tests
        run: cargo test --all-features
      - name: Run benchmarks
        run: cargo bench --no-run
      - name: Check coverage
        run: cargo tarpaulin --fail-under 90
```

### Test Matrix
```yaml
strategy:
  matrix:
    rust: [stable, nightly]
    os: [ubuntu-latest, macos-latest]
```

## Test Helpers

### Builder Pattern
```rust
struct OpportunityBuilder {
    actions: Vec<Action>,
    constraints: Option<Constraints>,
}

impl OpportunityBuilder {
    fn new() -> Self { /* ... */ }
    fn with_borrow(mut self, amount: u64, token: &str) -> Self { /* ... */ }
    fn with_swap(mut self, from: &str, to: &str, amount: u64) -> Self { /* ... */ }
    fn build(self) -> Opportunity { /* ... */ }
}

// Usage
let opp = OpportunityBuilder::new()
    .with_borrow(100, "WETH")
    .with_swap("WETH", "USDC", 100)
    .build();
```

### Assertion Helpers
```rust
fn assert_expression_structure<F>(expr: &Expr, check: F) 
where F: Fn(&Expr) -> bool 
{
    assert!(check(expr), "Expression structure mismatch");
}

fn assert_contains_action(expr: &Expr, action_type: &str) -> bool {
    // Recursively search for action type
}
```

## Debugging Support

### Test Logging
```rust
#[test]
fn test_with_logging() {
    env_logger::init();
    
    log::debug!("Starting test");
    let result = compile_opportunity(input);
    log::debug!("Result: {:?}", result);
    
    assert!(result.is_ok());
}
```

### Snapshot Testing
```rust
use insta::assert_json_snapshot;

#[test]
fn test_compiler_output_snapshot() {
    let input = include_str!("../fixtures/flash_loan.json");
    let output = compile_opportunity(input).unwrap();
    
    assert_json_snapshot!(output);
}
```

## Conclusion

This comprehensive testing strategy ensures the compiler is correct, performant, and robust. Regular execution of all test suites maintains quality as the system evolves.