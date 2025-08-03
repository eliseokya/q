# Makefile: Build, test, deploy automation
#
# Main commands for atomic-mesh-execution system
# Run 'make help' to see all available commands

.PHONY: help build test deploy clean

# Default target
help:
	@echo "Atomic Mesh Execution - Build System"
	@echo ""
	@echo "Available commands:"
	@echo "  make build          - Compile all contracts"
	@echo "  make test           - Run all tests"
	@echo "  make test-unit      - Run unit tests only"
	@echo "  make test-integration - Run integration tests"
	@echo "  make test-e2e       - Run end-to-end tests"
	@echo "  make test-gas       - Run tests with gas reporting"
	@echo "  make deploy-testnet - Deploy to testnets"
	@echo "  make deploy-mainnet - Deploy to mainnet (careful!)"
	@echo "  make verify         - Verify contracts on Etherscan"
	@echo "  make clean          - Clean build artifacts"
	@echo "  make audit          - Run security audit tools"
	@echo "  make coverage       - Generate test coverage report"
	@echo "  make docs           - Generate documentation"

# Build contracts
build:
	forge build

# Run all tests
test:
	forge test -vv

# Run specific test suites
test-unit:
	forge test --match-path "test/unit/**" -vv

test-integration:
	forge test --match-path "test/integration/**" -vv

test-e2e:
	cd test/e2e && npm test

# Test with gas reporting
test-gas:
	forge test --gas-report

# Deployment targets
deploy-testnet:
	./scripts/deploy/deploy-all.sh testnet

deploy-mainnet:
	@echo "⚠️  WARNING: About to deploy to MAINNET!"
	@echo "Press Ctrl+C to cancel, or Enter to continue..."
	@read confirm
	./scripts/deploy/deploy-all.sh mainnet --verify

# Clean build artifacts
clean:
	forge clean
	rm -rf out cache

# Security audit
audit:
	slither contracts/
	mythril analyze contracts/core/AtomicExecutor.sol

# Coverage report
coverage:
	forge coverage --report lcov
	genhtml lcov.info -o coverage

# Generate documentation
docs:
	forge doc

# Implementation notes to be added later