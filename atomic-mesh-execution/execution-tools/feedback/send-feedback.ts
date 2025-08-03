#!/usr/bin/env node

/**
 * feedback-sender: Sends execution results to detection system
 * 
 * This tool collects execution results and sends them back to the
 * detection system for learning and improvement. It helps the detection
 * system understand which opportunities succeed and why.
 * 
 * Input: Execution results from bundle-executor
 * {
 *   "bundle_id": "uuid",
 *   "opportunity_id": "uuid",
 *   "status": "success|failure|partial",
 *   "actual_profit": "125.30",
 *   "gas_used": {
 *     "ethereum": "250000",
 *     "arbitrum": "1500000"
 *   },
 *   "execution_time": 398,
 *   "bridge_used": "atomic_mesh",
 *   "slippage": "0.15%",
 *   "timestamp": "1234567890"
 * }
 * 
 * Output: Formatted feedback for detection system
 * {
 *   "bundle_id": "uuid",
 *   "opportunity_id": "uuid", 
 *   "success": true,
 *   "profit_accuracy": 0.83,  // actual/expected
 *   "gas_accuracy": 0.95,     // estimated/actual
 *   "execution_metrics": {
 *     "time_ms": 398,
 *     "chains_touched": 2,
 *     "protocols_used": ["aave", "uniswap", "curve"],
 *     "bridge_performance": "fast"
 *   },
 *   "failure_reason": null,
 *   "learnings": {
 *     "gas_adjustment_factor": 1.05,
 *     "slippage_observed": 0.0015,
 *     "optimal_timing": "block_start"
 *   }
 * }
 * 
 * Features:
 * - Analyzes success/failure patterns
 * - Calculates accuracy metrics
 * - Identifies optimization opportunities
 * - Provides actionable feedback
 * - Maintains execution history
 * - Supports batch feedback
 * 
 * Usage:
 *   bundle-executor | feedback-sender | nc detection-system 9999
 *   feedback-sender --batch < execution-results.jsonl
 */

// Implementation will be added later