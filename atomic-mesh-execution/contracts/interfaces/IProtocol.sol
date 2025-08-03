// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

/**
 * @title IProtocol
 * @notice Unified protocol interface
 * @dev Standard interface for all protocol adapters:
 *      - Swap operations
 *      - Flash loan operations
 *      - Liquidity operations
 *      - Query functions
 * 
 * Standard functions:
 * - swap: Execute token swaps
 * - flashLoan: Initiate flash loans
 * - addLiquidity: Provide liquidity
 * - removeLiquidity: Withdraw liquidity
 * - getPrice: Query current prices
 * - getLiquidity: Check available liquidity
 * 
 * All protocol adapters must implement this interface
 * for compatibility with the execution system.
 */
interface IProtocol {
    // Implementation will be added later
}