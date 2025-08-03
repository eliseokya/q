# Migration Plan: Current → Three-Module Structure

## Overview
This document outlines how to migrate from the current structure to the reorganized three-module architecture.

## Migration Steps

### Phase 1: Create Module Structure

```bash
# Create module directories
mkdir -p module-1-dsl-compilation/{pattern-library,pattern-matcher,condition-validator,bundle-generator,feedback,pipeline}
mkdir -p module-2-execution-tools/{bundle-composer,gas-optimizer,profitability-checker,bridge-selector,execution-simulator,bundle-executor,state-monitor,feedback,config,pipeline}
mkdir -p module-3-contracts/{src,test,script,deployments,config,feedback}
mkdir -p shared/{interfaces,config,utils}
mkdir -p integration/{feedback-aggregator,tests}
```

### Phase 2: Module 1 - DSL Compilation (NEW)

This is a new module that needs to be created:

1. **Create pattern-library/**
   - Import patterns.json from Lean exports
   - Add proof certificates
   - Create update script to sync with maths/DSL/Patterns/

2. **Create pattern-matcher/**
   - Implement O(1) pattern matching
   - Move pattern identification logic here

3. **Create condition-validator/**
   - Implement well-formedness checks
   - Value preservation validation
   - Bridge validity checks

4. **Create bundle-generator/**
   - Generate validated bundles from patterns
   - Add atomicity proof references

### Phase 3: Module 2 - Execution Tools

Move and reorganize existing tools:

```bash
# Move tools to module-2
mv tools/bundle-composer module-2-execution-tools/bundle-composer/bin/
mv tools/gas-optimizer module-2-execution-tools/gas-optimizer/bin/
mv tools/profitability-checker module-2-execution-tools/profitability-checker/bin/
mv tools/bridge-selector module-2-execution-tools/bridge-selector/bin/
mv tools/execution-simulator module-2-execution-tools/execution-simulator/bin/
mv tools/bundle-executor module-2-execution-tools/bundle-executor/bin/
mv tools/state-monitor module-2-execution-tools/state-monitor/bin/

# Move feedback tools
mv tools/feedback-sender module-2-execution-tools/feedback/
```

Create proper source structure for each tool:
- Add src/ directories with TypeScript implementations
- Add test/ directories
- Create tool-specific configs

### Phase 4: Module 3 - Contracts

Reorganize contracts with better structure:

```bash
# Move contracts
mv contracts/core module-3-contracts/src/core
mv contracts/protocols module-3-contracts/src/protocols
mv contracts/bridges module-3-contracts/src/bridges
mv contracts/chains module-3-contracts/src/chains
mv contracts/execution module-3-contracts/src/execution
mv contracts/protection module-3-contracts/src/protection

# Move interfaces
mkdir -p module-3-contracts/src/protocols/interfaces
mv contracts/interfaces/IProtocol.sol module-3-contracts/src/protocols/interfaces/

# Move tests
mv test/* module-3-contracts/test/

# Move scripts
mv scripts/deploy/* module-3-contracts/script/
```

### Phase 5: Shared Resources

Move shared configurations:

```bash
# Move to shared config
mv config/chains.json shared/config/
mv config/tokens.json shared/config/
mv config/detection-interface.json shared/config/

# Module-specific configs stay in their modules
mv config/gas-config.json module-2-execution-tools/config/
mv config/bridge-config.json module-2-execution-tools/bridge-selector/config/
mv config/addresses.json module-3-contracts/config/
```

### Phase 6: Integration Layer

Create integration components:

1. **Create pipeline.sh**
   ```bash
   #!/bin/bash
   # Main execution pipeline
   
   # Module 1: DSL Compilation
   cat opportunity.json | module-1-dsl-compilation/pipeline/dsl-compile | \
   
   # Module 2: Execution Tools  
   module-2-execution-tools/pipeline/execute-tools | \
   
   # Module 3: Contract Execution
   module-3-contracts/bin/execute-contract
   ```

2. **Create feedback-aggregator/**
   - Collects feedback from all modules
   - Sends unified feedback to detection system

### Phase 7: Update Build System

1. **Root Makefile**
   ```makefile
   all: module-1 module-2 module-3
   
   module-1:
       $(MAKE) -C module-1-dsl-compilation
   
   module-2:
       $(MAKE) -C module-2-execution-tools
       
   module-3:
       $(MAKE) -C module-3-contracts
   ```

2. **Module Makefiles**
   - Each module gets its own Makefile
   - Independent build/test/deploy targets

### Phase 8: Update Documentation

1. Move and update documentation:
   ```bash
   mv README.md docs/README.md
   mv higher_level_architecture.md docs/
   ```

2. Create module-specific docs:
   - module-1-dsl.md
   - module-2-tools.md  
   - module-3-contracts.md
   - feedback-integration.md

### Phase 9: Remove Old Structure

```bash
# After verification, remove old directories
rm -rf tools/
rm -rf contracts/
rm -rf monitoring/
rm -rf scripts/deploy/
rm -rf config/
```

## Validation Checklist

- [ ] All tools moved to appropriate modules
- [ ] Feedback mechanisms integrated in each module
- [ ] Shared resources properly separated
- [ ] Build system updated and working
- [ ] Documentation reflects new structure
- [ ] Integration pipeline tested end-to-end
- [ ] No functionality lost in migration

## Benefits After Migration

1. **Clear Separation**: Each module has a single, clear purpose
2. **Independent Development**: Modules can evolve separately
3. **Better Testing**: Module-specific test suites
4. **Integrated Feedback**: Learning built into every stage
5. **Unix Philosophy**: Small, focused tools throughout