// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

/**
 * @title IAtomicExecutor
 * @notice Core execution interface
 * @dev Defines the standard interface for atomic execution:
 *      - Bundle execution entry point
 *      - Callback interfaces for flash loans
 *      - Status query functions
 *      - Emergency functions
 * 
 * Core functions:
 * - executeBundle: Main entry point for execution
 * - getExecutionStatus: Query bundle status
 * - cancelExecution: Emergency cancellation
 * - withdrawProfit: Claim arbitrage profits
 * 
 * Events:
 * - BundleExecuted: Successful execution
 * - BundleFailed: Failed execution with reason
 * - ProfitWithdrawn: Profit distribution
 * - EmergencyPause: System paused
 */
interface IAtomicExecutor {
    // Implementation will be added later
}