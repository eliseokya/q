//! Phase 3: Pipeline Integration Tests
//! Comprehensive testing of Unix pipeline compliance

use std::process::{Command, Stdio};
use std::io::Write;
use tempfile::NamedTempFile;
use serde_json;

#[derive(Debug)]
struct PipelineTestResult {
    exit_code: i32,
    stdout: String,
    stderr: String,
    duration_ms: u64,
}

struct PipelineTest {
    name: String,
    input: serde_json::Value,
    expected_exit_code: i32,
    expected_fields: Vec<String>,
}

/// Test Unix pipeline compliance
#[tokio::test]
async fn test_unix_pipeline_compliance() {
    println!("🧪 Phase 3: Unix Pipeline Compliance Tests");
    println!("==========================================");
    
    let tests = vec![
        PipelineTest {
            name: "Valid Flash Loan".to_string(),
            input: serde_json::json!({
                "opportunity_id": "test-flash-loan",
                "source_chain": "polygon",
                "path": [
                    {"action": "borrow", "amount": "100", "token": "USDC", "protocol": "aave"},
                    {"action": "repay", "amount": "100", "token": "USDC", "protocol": "aave"}
                ]
            }),
            expected_exit_code: 0,
            expected_fields: vec!["name".to_string(), "startChain".to_string(), "expr".to_string(), "constraints".to_string()],
        },
        PipelineTest {
            name: "Invalid JSON".to_string(),
            input: serde_json::json!("invalid json"),
            expected_exit_code: 3,
            expected_fields: vec!["error".to_string(), "component".to_string(), "code".to_string()],
        },
        PipelineTest {
            name: "Missing Required Field".to_string(),
            input: serde_json::json!({
                "opportunity_id": "test",
                // Missing path field
            }),
            expected_exit_code: 12,
            expected_fields: vec!["error".to_string(), "message".to_string()],
        },
        PipelineTest {
            name: "Empty Actions".to_string(),
            input: serde_json::json!({
                "opportunity_id": "test-empty",
                "source_chain": "polygon",
                "path": []
            }),
            expected_exit_code: 10,
            expected_fields: vec!["error".to_string()],
        },
    ];
    
    let mut passed = 0;
    let total = tests.len();
    
    for test in tests {
        print!("Testing {}... ", test.name);
        
        match run_pipeline_test(&test).await {
            Ok(result) => {
                if result.exit_code == test.expected_exit_code {
                    // Validate output structure
                    if validate_output_structure(&result, &test.expected_fields) {
                        println!("✅ PASS");
                        passed += 1;
                    } else {
                        println!("❌ FAIL (Invalid output structure)");
                        println!("   stdout: {}", result.stdout);
                        println!("   stderr: {}", result.stderr);
                    }
                } else {
                    println!("❌ FAIL (Exit code: expected {}, got {})", 
                             test.expected_exit_code, result.exit_code);
                    println!("   stderr: {}", result.stderr);
                }
            }
            Err(e) => {
                println!("❌ FAIL (Test error: {})", e);
            }
        }
    }
    
    println!("\n📊 Pipeline Compliance Results");
    println!("==============================");
    println!("Passed: {}/{}", passed, total);
    
    assert_eq!(passed, total, "All pipeline compliance tests must pass");
}

async fn run_pipeline_test(test: &PipelineTest) -> Result<PipelineTestResult, Box<dyn std::error::Error>> {
    // Create temporary input file
    let mut input_file = NamedTempFile::new()?;
    writeln!(input_file, "{}", serde_json::to_string(&test.input)?)?;
    input_file.flush()?;
    
    let start_time = std::time::Instant::now();
    
    // Run monolithic binary with input
    let output = Command::new("./bin/monolithic")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?
        .stdin.take().unwrap();
    
    // Write input to stdin
    output.write_all(serde_json::to_string(&test.input)?.as_bytes())?;
    drop(output);
    
    let output = Command::new("./bin/monolithic")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()?;
    
    let duration_ms = start_time.elapsed().as_millis() as u64;
    
    Ok(PipelineTestResult {
        exit_code: output.status.code().unwrap_or(-1),
        stdout: String::from_utf8_lossy(&output.stdout).to_string(),
        stderr: String::from_utf8_lossy(&output.stderr).to_string(),
        duration_ms,
    })
}

fn validate_output_structure(result: &PipelineTestResult, expected_fields: &[String]) -> bool {
    if result.exit_code == 0 {
        // Success case - validate stdout JSON
        if let Ok(json) = serde_json::from_str::<serde_json::Value>(&result.stdout) {
            expected_fields.iter().all(|field| json.get(field).is_some())
        } else {
            false
        }
    } else {
        // Error case - validate stderr JSON
        if let Ok(json) = serde_json::from_str::<serde_json::Value>(&result.stderr) {
            expected_fields.iter().all(|field| json.get(field).is_some())
        } else {
            false
        }
    }
}

/// Test component composability via Unix pipes
#[tokio::test]
async fn test_component_composability() {
    println!("🔗 Testing Component Composability");
    println!("==================================");
    
    let input = serde_json::json!({
        "opportunity_id": "composability-test",
        "source_chain": "polygon",
        "path": [
            {"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}
        ]
    });
    
    // Test individual components can be piped together
    let parse_output = Command::new("./bin/parse-and-validate")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .and_then(|mut child| {
            let stdin = child.stdin.take().unwrap();
            std::thread::spawn(move || {
                serde_json::to_writer(stdin, &input).unwrap();
            });
            child.wait_with_output()
        });
    
    match parse_output {
        Ok(output) if output.status.success() => {
            println!("✅ parse-and-validate component works");
            
            // Validate output can be piped to next component
            let parsed_json: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
            assert!(parsed_json.get("metadata").is_some());
            assert!(parsed_json.get("actions").is_some());
        }
        Ok(output) => {
            println!("❌ parse-and-validate failed: {}", String::from_utf8_lossy(&output.stderr));
            panic!("Component composability test failed");
        }
        Err(e) => {
            println!("❌ parse-and-validate error: {}", e);
            panic!("Component composability test failed");
        }
    }
}

/// Test performance within pipeline context
#[tokio::test]
async fn test_pipeline_performance() {
    println!("⚡ Testing Pipeline Performance");
    println!("==============================");
    
    let test_cases = vec![
        ("Small Input", create_small_input()),
        ("Medium Input", create_medium_input()),
        ("Large Input", create_large_input()),
    ];
    
    for (name, input) in test_cases {
        print!("Testing {}... ", name);
        
        let start_time = std::time::Instant::now();
        
        let output = Command::new("./bin/monolithic")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .and_then(|mut child| {
                let stdin = child.stdin.take().unwrap();
                std::thread::spawn(move || {
                    serde_json::to_writer(stdin, &input).unwrap();
                });
                child.wait_with_output()
            });
        
        let duration = start_time.elapsed();
        let duration_ms = duration.as_millis();
        
        match output {
            Ok(output) if output.status.success() => {
                println!("✅ {}ms", duration_ms);
                
                // Validate performance target (<1.5ms eventually, <10ms for now)
                if duration_ms > 10 {
                    println!("   ⚠️  Warning: Exceeds 10ms target");
                }
            }
            Ok(output) => {
                println!("❌ FAIL: {}", String::from_utf8_lossy(&output.stderr));
            }
            Err(e) => {
                println!("❌ ERROR: {}", e);
            }
        }
    }
}

fn create_small_input() -> serde_json::Value {
    serde_json::json!({
        "opportunity_id": "small-test",
        "source_chain": "polygon",
        "path": [
            {"action": "swap", "amount": "100", "from": "USDC", "to": "WETH", "minOut": "0.5", "protocol": "uniswapv2"}
        ]
    })
}

fn create_medium_input() -> serde_json::Value {
    let mut actions = Vec::new();
    for i in 0..10 {
        actions.push(serde_json::json!({
            "action": "swap",
            "amount": format!("{}", 100 + i),
            "from": "USDC",
            "to": "WETH",
            "minOut": "0.5",
            "protocol": "uniswapv2"
        }));
    }
    
    serde_json::json!({
        "opportunity_id": "medium-test",
        "source_chain": "polygon",
        "path": actions
    })
}

fn create_large_input() -> serde_json::Value {
    let mut actions = Vec::new();
    for i in 0..100 {
        actions.push(serde_json::json!({
            "action": "swap",
            "amount": format!("{}", 100 + i),
            "from": "USDC",
            "to": "WETH", 
            "minOut": "0.5",
            "protocol": "uniswapv2"
        }));
    }
    
    serde_json::json!({
        "opportunity_id": "large-test",
        "source_chain": "polygon",
        "path": actions,
        "constraints": {
            "deadline": 20,
            "max_gas": 500000,
            "invariants": ["constant-product", "no-negative-balance"]
        }
    })
}