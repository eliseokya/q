//! Performance optimization utilities for Phase 4
//! 
//! This module contains optimized versions of core functionality
//! targeting the <1.5ms total compilation time.

pub mod fast_json;
pub mod rational_simd;
pub mod memory_pool;
pub mod string_interning;

use std::time::Instant;

/// Performance measurement utilities
pub struct PerformanceMeasurement {
    start: Instant,
    checkpoints: Vec<(&'static str, Instant)>,
}

impl PerformanceMeasurement {
    pub fn new() -> Self {
        Self {
            start: Instant::now(),
            checkpoints: Vec::new(),
        }
    }
    
    pub fn checkpoint(&mut self, name: &'static str) {
        self.checkpoints.push((name, Instant::now()));
    }
    
    pub fn report(&self, component: &str) {
        let total = self.start.elapsed();
        println!("🔥 {} Performance Report:", component);
        println!("   Total: {}μs", total.as_micros());
        
        let mut last_time = self.start;
        for (name, time) in &self.checkpoints {
            let duration = time.duration_since(last_time);
            println!("   {}: {}μs", name, duration.as_micros());
            last_time = *time;
        }
        
        // Performance targets
        let target_us = match component {
            "parse-and-validate" => 300,
            "transform-actions" => 400,
            "build-expression" => 600,
            "assemble-bundle" => 200,
            "monolithic" => 1500,
            _ => 1000,
        };
        
        let actual_us = total.as_micros();
        if actual_us <= target_us as u128 {
            println!("   ✅ Target met: {}μs ≤ {}μs", actual_us, target_us);
        } else {
            println!("   ❌ Target missed: {}μs > {}μs", actual_us, target_us);
        }
    }
}

/// Macro for easy performance measurement
#[macro_export]
macro_rules! perf_measure {
    ($perf:expr, $name:expr, $code:block) => {
        $perf.checkpoint(concat!("start_", $name));
        let result = $code;
        $perf.checkpoint(concat!("end_", $name));
        result
    };
}