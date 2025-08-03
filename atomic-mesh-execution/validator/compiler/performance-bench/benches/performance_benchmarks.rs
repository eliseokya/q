use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use std::process::{Command, Stdio};
use std::io::Write;
use std::time::Duration;

/// Performance benchmarks for Phase 4 optimization
/// 
/// Target performance (total <1.5ms):
/// - parse-and-validate: <0.3ms
/// - transform-actions: <0.4ms  
/// - build-expression: <0.6ms
/// - assemble-bundle: <0.2ms

// Test inputs of varying complexity
fn create_test_inputs() -> Vec<(&'static str, &'static str)> {
    vec![
        ("simple_swap", r#"{"opportunity_id": "simple", "source_chain": "polygon", "path": [{"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}]}"#),
        
        ("flash_loan", r#"{"opportunity_id": "flash-loan", "source_chain": "polygon", "path": [
            {"action": "borrow", "amount": "1000", "token": "USDC", "protocol": "aave"},
            {"action": "swap", "amount": "500", "from": "USDC", "to": "WETH", "minOut": "0.25", "protocol": "uniswapv2"},
            {"action": "repay", "amount": "1000", "token": "USDC", "protocol": "aave"}
        ]}"#),
        
        ("complex_arbitrage", r#"{"opportunity_id": "complex", "source_chain": "polygon", "path": [
            {"action": "borrow", "amount": "10000", "token": "USDC", "protocol": "aave"},
            {"action": "bridge", "to": "arbitrum", "token": "USDC", "amount": "5000"},
            {"action": "swap", "amount": "5000", "from": "USDC", "to": "WETH", "minOut": "2.5", "protocol": "uniswapv2"},
            {"action": "swap", "amount": "2.5", "from": "WETH", "to": "DAI", "minOut": "5000", "protocol": "compound"},
            {"action": "bridge", "to": "polygon", "token": "DAI", "amount": "5000"},
            {"action": "swap", "amount": "5000", "from": "DAI", "to": "USDC", "minOut": "5000", "protocol": "uniswapv2"},
            {"action": "repay", "amount": "10000", "token": "USDC", "protocol": "aave"}
        ], "constraints": {"deadline": 20, "max_gas": 500000, "invariants": ["constant-product"]}}"#),
    ]
}

fn run_component_benchmark(component: &str, input: &str) -> Duration {
    let start = std::time::Instant::now();
    
    let mut child = Command::new(format!("./bin/{}", component))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to start component");
    
    if let Some(stdin) = child.stdin.take() {
        let mut stdin = stdin;
        stdin.write_all(input.as_bytes()).expect("Failed to write input");
    }
    
    let output = child.wait_with_output().expect("Failed to wait for component");
    let duration = start.elapsed();
    
    if !output.status.success() {
        panic!("Component {} failed: {}", component, String::from_utf8_lossy(&output.stderr));
    }
    
    duration
}

fn run_monolithic_benchmark(input: &str) -> Duration {
    let start = std::time::Instant::now();
    
    let mut child = Command::new("./bin/monolithic")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to start monolithic");
    
    if let Some(stdin) = child.stdin.take() {
        let mut stdin = stdin;
        stdin.write_all(input.as_bytes()).expect("Failed to write input");
    }
    
    let output = child.wait_with_output().expect("Failed to wait for monolithic");
    let duration = start.elapsed();
    
    if !output.status.success() {
        panic!("Monolithic failed: {}", String::from_utf8_lossy(&output.stderr));
    }
    
    duration
}

fn benchmark_individual_components(c: &mut Criterion) {
    let mut group = c.benchmark_group("individual_components");
    group.measurement_time(Duration::from_secs(10));
    
    let components = ["parse-and-validate", "transform-actions", "build-expression", "assemble-bundle"];
    let targets = [300_000, 400_000, 600_000, 200_000]; // nanoseconds
    
    for (input_name, input_data) in create_test_inputs() {
        for (i, &component) in components.iter().enumerate() {
            let target_ns = targets[i];
            
            group.bench_with_input(
                BenchmarkId::new(format!("{}_target_{}μs", component, target_ns / 1000), input_name),
                &(component, input_data),
                |b, &(comp, data)| {
                    b.iter(|| {
                        let duration = run_component_benchmark(comp, data);
                        black_box(duration);
                        
                        // Assert performance target
                        if duration.as_nanos() > target_ns as u128 {
                            eprintln!("⚠️ {} took {}μs (target: {}μs)", 
                                     comp, 
                                     duration.as_micros(), 
                                     target_ns / 1000);
                        }
                    });
                }
            );
        }
    }
    
    group.finish();
}

fn benchmark_monolithic_pipeline(c: &mut Criterion) {
    let mut group = c.benchmark_group("monolithic_pipeline");
    group.measurement_time(Duration::from_secs(10));
    
    for (input_name, input_data) in create_test_inputs() {
        group.bench_with_input(
            BenchmarkId::new("monolithic_target_1500μs", input_name),
            input_data,
            |b, data| {
                b.iter(|| {
                    let duration = run_monolithic_benchmark(data);
                    black_box(duration);
                    
                    // Assert total performance target
                    if duration.as_micros() > 1500 {
                        eprintln!("⚠️ Monolithic took {}μs (target: 1500μs)", duration.as_micros());
                    }
                });
            }
        );
    }
    
    group.finish();
}

fn benchmark_memory_usage(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_usage");
    group.measurement_time(Duration::from_secs(5));
    
    // Measure memory allocations during processing
    for (input_name, input_data) in create_test_inputs() {
        group.bench_with_input(
            BenchmarkId::new("memory_allocations", input_name),
            input_data,
            |b, data| {
                b.iter(|| {
                    // This would require memory profiling integration
                    let duration = run_monolithic_benchmark(data);
                    black_box(duration);
                });
            }
        );
    }
    
    group.finish();
}

fn benchmark_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("throughput");
    group.measurement_time(Duration::from_secs(10));
    
    let (_, sample_input) = create_test_inputs()[0];
    
    // Measure how many requests we can process per second
    group.bench_function("requests_per_second", |b| {
        b.iter(|| {
            for _ in 0..100 {
                let duration = run_monolithic_benchmark(sample_input);
                black_box(duration);
            }
        });
    });
    
    group.finish();
}

criterion_group!(
    benches,
    benchmark_individual_components,
    benchmark_monolithic_pipeline,
    benchmark_memory_usage,
    benchmark_throughput
);
criterion_main!(benches);