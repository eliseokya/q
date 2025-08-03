// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

/**
 * @title IBridge
 * @notice Unified bridge interface
 * @dev Standard interface for all bridge implementations:
 *      - Cross-chain transfer initiation
 *      - Callback handling
 *      - Status queries
 *      - Fee calculations
 * 
 * Core functions:
 * - bridgeTokens: Initiate cross-chain transfer
 * - estimateFee: Calculate bridge fees
 * - getTransferStatus: Query transfer status
 * - cancelTransfer: Cancel pending transfer
 * - claimTransfer: Claim completed transfer
 * 
 * Callbacks:
 * - onTokensReceived: Handle incoming transfers
 * - onTransferComplete: Finalize transfer
 * 
 * All bridges must implement this interface
 * for router compatibility.
 */
interface IBridge {
    // Implementation will be added later
}