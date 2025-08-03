// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

/**
 * @title IFlashLoanReceiver
 * @notice Unified flash loan callback
 * @dev Standard callback interface for all flash loan protocols:
 *      - Receives borrowed funds
 *      - Executes arbitrage logic
 *      - Repays loan with fee
 *      - Handles multiple protocols
 * 
 * Callback pattern:
 * 1. Protocol sends borrowed tokens
 * 2. Callback executes arbitrage
 * 3. Callback repays loan + fee
 * 4. Transaction reverts if repayment fails
 * 
 * This interface abstracts away protocol-specific
 * callbacks (executeOperation, onFlashLoan, etc.)
 * into a unified interface for the router.
 * 
 * Security: Only callable by registered protocols
 */
interface IFlashLoanReceiver {
    // Implementation will be added later
}