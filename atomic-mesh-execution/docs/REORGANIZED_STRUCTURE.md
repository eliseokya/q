# Atomic Mesh Execution - Reorganized Three-Module Structure

## Overview
This document shows the reorganized structure following the three-module architecture with integrated feedback to the detection system.

```
atomic-mesh-execution/
│
├── module-1-dsl-compilation/               # Mathematical Validation & Pattern Matching
│   ├── README.md                           # Module documentation
│   ├── Makefile                            # Module-specific build
│   │
│   ├── pattern-library/                    # Pre-proven patterns from Lean
│   │   ├── patterns.json                   # Exported pattern definitions
│   │   ├── proofs/                         # Proof certificates
│   │   │   ├── flash-loan.proof
│   │   │   ├── cross-chain-arb.proof
│   │   │   └── triangular-arb.proof
│   │   └── update-patterns.sh              # Sync with Lean exports
│   │
│   ├── pattern-matcher/                    # O(1) pattern identification
│   │   ├── src/
│   │   │   ├── matcher.ts
│   │   │   └── pattern-index.ts
│   │   ├── test/
│   │   └── bin/
│   │       └── pattern-match               # Unix executable
│   │
│   ├── condition-validator/                # Well-formedness checking
│   │   ├── src/
│   │   │   ├── validator.ts
│   │   │   └── conditions/
│   │   │       ├── value-preserving.ts
│   │   │       ├── bridge-validity.ts
│   │   │       └── timing-feasible.ts
│   │   ├── test/
│   │   └── bin/
│   │       └── validate-conditions         # Unix executable
│   │
│   ├── bundle-generator/                   # Generate validated bundles
│   │   ├── src/
│   │   │   └── generator.ts
│   │   ├── test/
│   │   └── bin/
│   │       └── generate-bundle             # Unix executable
│   │
│   ├── feedback/                           # Report validation failures to detection
│   │   ├── pattern-not-found.sh
│   │   ├── validation-failed.sh
│   │   └── send-feedback.ts
│   │
│   └── pipeline/                           # Module pipeline script
│       └── dsl-compile                     # Main entry point
│
├── module-2-execution-tools/               # Optimization & Orchestration
│   ├── README.md
│   ├── Makefile
│   │
│   ├── bundle-composer/                    # Format bundles for execution
│   │   ├── src/
│   │   ├── test/
│   │   └── bin/
│   │       └── bundle-composer
│   │
│   ├── gas-optimizer/                      # Apply categorical optimizations
│   │   ├── src/
│   │   │   ├── path-optimizer.ts          # Colimit-based optimization
│   │   │   ├── batch-optimizer.ts         # Monoidal batching
│   │   │   ├── parallel-analyzer.ts       # Independence analysis
│   │   │   └── bridge-adjunction.ts       # Optimal bridge selection
│   │   ├── config/
│   │   │   └── gas-tables.json
│   │   ├── test/
│   │   └── bin/
│   │       └── gas-optimizer
│   │
│   ├── profitability-checker/              # Economic validation
│   │   ├── src/
│   │   ├── test/
│   │   └── bin/
│   │       └── profitability-checker
│   │
│   ├── bridge-selector/                    # Choose optimal bridge
│   │   ├── src/
│   │   ├── config/
│   │   │   └── bridge-config.json
│   │   ├── test/
│   │   └── bin/
│   │       └── bridge-selector
│   │
│   ├── execution-simulator/                # Simulate before execution
│   │   ├── src/
│   │   ├── test/
│   │   └── bin/
│   │       └── execution-simulator
│   │
│   ├── bundle-executor/                    # Submit to blockchain
│   │   ├── src/
│   │   ├── test/
│   │   └── bin/
│   │       └── bundle-executor
│   │
│   ├── state-monitor/                      # Monitor chain states
│   │   ├── src/
│   │   └── bin/
│   │       └── state-monitor
│   │
│   ├── feedback/                           # Report execution issues to detection
│   │   ├── gas-too-high.sh
│   │   ├── unprofitable.sh
│   │   ├── simulation-failed.sh
│   │   └── send-feedback.ts
│   │
│   ├── config/                             # Shared configurations
│   │   ├── gas-config.json
│   │   ├── profitability-thresholds.json
│   │   └── chain-configs.json
│   │
│   └── pipeline/                           # Module pipeline script
│       └── execute-tools                   # Main entry point
│
├── module-3-contracts/                     # On-chain Execution
│   ├── README.md
│   ├── foundry.toml                        # Foundry configuration
│   ├── Makefile
│   │
│   ├── src/                                # Contract source files
│   │   ├── core/
│   │   │   ├── AtomicExecutor.sol
│   │   │   ├── BundleRegistry.sol
│   │   │   └── ExecutionOrchestrator.sol
│   │   │
│   │   ├── protocols/
│   │   │   ├── interfaces/
│   │   │   │   └── IProtocol.sol
│   │   │   ├── AaveV3Complete.sol
│   │   │   ├── UniswapComplete.sol
│   │   │   ├── CurveComplete.sol
│   │   │   ├── CompoundV3Complete.sol
│   │   │   ├── BalancerComplete.sol
│   │   │   └── ProtocolRegistry.sol
│   │   │
│   │   ├── bridges/
│   │   │   ├── interfaces/
│   │   │   │   └── IBridge.sol
│   │   │   ├── AtomicMeshBridge.sol
│   │   │   ├── DeBridge.sol
│   │   │   ├── BridgeRouter.sol
│   │   │   └── BridgeRegistry.sol
│   │   │
│   │   ├── chains/
│   │   │   ├── Ethereum.sol
│   │   │   ├── Arbitrum.sol
│   │   │   ├── Polygon.sol
│   │   │   ├── Base.sol
│   │   │   └── Optimism.sol
│   │   │
│   │   ├── execution/
│   │   │   ├── FlashLoanRouter.sol
│   │   │   ├── GasProfitability.sol
│   │   │   ├── StateValidator.sol
│   │   │   ├── NonceManager.sol
│   │   │   ├── RecoveryManager.sol
│   │   │   └── CapitalManager.sol
│   │   │
│   │   └── protection/
│   │       ├── StateCommitment.sol
│   │       ├── TimingRandomizer.sol
│   │       └── EmergencyPause.sol
│   │
│   ├── test/                               # Contract tests
│   │   ├── unit/
│   │   ├── integration/
│   │   └── e2e/
│   │
│   ├── script/                             # Deployment scripts
│   │   ├── Deploy.s.sol
│   │   ├── DeployProtocols.s.sol
│   │   └── DeployBridges.s.sol
│   │
│   ├── deployments/                        # Deployment artifacts
│   │   ├── mainnet/
│   │   └── testnet/
│   │
│   ├── config/                             # Contract configurations
│   │   ├── addresses.json
│   │   ├── protocol-params.json
│   │   └── gas-limits.json
│   │
│   └── feedback/                           # Report contract failures to detection
│       ├── revert-analyzer.ts
│       ├── slippage-reporter.ts
│       └── send-feedback.ts
│
├── shared/                                 # Shared across modules
│   ├── interfaces/                         # Common TypeScript interfaces
│   │   ├── bundle.ts
│   │   ├── opportunity.ts
│   │   └── feedback.ts
│   │
│   ├── config/                             # Global configurations
│   │   ├── chains.json
│   │   ├── tokens.json
│   │   └── detection-interface.json
│   │
│   └── utils/                              # Shared utilities
│       ├── logger.ts
│       ├── metrics.ts
│       └── error-handler.ts
│
├── integration/                            # Cross-module integration
│   ├── pipeline.sh                         # Main execution pipeline
│   ├── feedback-aggregator/                # Aggregate feedback from all modules
│   │   ├── src/
│   │   │   └── aggregator.ts
│   │   └── bin/
│   │       └── aggregate-feedback
│   │
│   └── tests/                              # End-to-end integration tests
│       ├── full-flow.test.ts
│       └── failure-modes.test.ts
│
├── scripts/                                # Operational scripts
│   ├── deploy-all.sh                       # Deploy entire system
│   ├── start-system.sh                     # Start all modules
│   ├── stop-system.sh                      # Stop all modules
│   ├── emergency-pause.sh                  # Emergency shutdown
│   └── sync-with-detection.sh              # Sync with detection system
│
├── docs/                                   # Documentation
│   ├── README.md                           # Main documentation
│   ├── higher_level_architecture.md        # System architecture
│   ├── module-1-dsl.md                     # DSL module guide
│   ├── module-2-tools.md                   # Tools module guide
│   ├── module-3-contracts.md               # Contracts module guide
│   └── feedback-integration.md             # Feedback system guide
│
├── Makefile                                # Root Makefile
├── package.json                            # Node.js dependencies
├── .env.example                            # Environment template
└── .gitignore                              # Git ignore rules
```

## Module Descriptions

### Module 1: DSL Compilation
- **Purpose**: Pattern match opportunities against pre-proven patterns
- **Input**: Opportunity JSON from detection system
- **Output**: Validated bundle JSON or rejection feedback
- **Feedback**: Reports pattern mismatches and validation failures

### Module 2: Execution Tools
- **Purpose**: Optimize and orchestrate validated bundles
- **Input**: Validated bundle JSON from Module 1
- **Output**: Optimized bundle for contract execution or rejection feedback
- **Feedback**: Reports unprofitability, high gas, simulation failures

### Module 3: Contracts
- **Purpose**: Execute bundles on-chain atomically
- **Input**: Optimized bundle from Module 2
- **Output**: Execution results or revert feedback
- **Feedback**: Reports reverts, slippage, and execution failures

## Key Changes from Current Structure

1. **Clear Module Boundaries**: Each module is self-contained with its own README, Makefile, and tests
2. **Integrated Feedback**: Each module has a feedback/ directory for reporting to detection
3. **Unix Philosophy**: Each sub-component is a separate tool with single responsibility
4. **Shared Resources**: Common configs and interfaces in shared/ directory
5. **Pipeline Integration**: Clear pipeline scripts showing data flow between modules
6. **No Separate Monitoring**: Monitoring integrated as feedback throughout modules

## Data Flow

```
Detection System
    ↓ (Opportunity JSON)
Module 1: DSL Compilation
    ↓ (Validated Bundle JSON)
    ↪ (Rejection → Feedback to Detection)
Module 2: Execution Tools
    ↓ (Optimized Bundle JSON)
    ↪ (Failure → Feedback to Detection)
Module 3: Contracts
    ↓ (Execution Result)
    ↪ (Revert → Feedback to Detection)
Feedback Aggregator
    ↓ (All Feedback)
Detection System (learns and improves)
```

## Benefits of Reorganization

1. **Modularity**: Each module can be developed, tested, and deployed independently
2. **Clear Interfaces**: JSON flows between modules with well-defined schemas
3. **Integrated Learning**: Detection system receives feedback from every stage
4. **Unix Philosophy**: Many small tools that do one thing well
5. **Maintainability**: Clear structure makes the system easier to understand and modify