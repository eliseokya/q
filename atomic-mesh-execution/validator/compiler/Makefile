.PHONY: all build test clean run-example

# Default target
all: build

# Build all components
build:
	@echo "Building compiler components..."
	@./scripts/build.sh

# Run tests
test:
	@echo "Running tests..."
	@./scripts/test.sh

# Clean build artifacts
clean:
	@echo "Cleaning build artifacts..."
	@cargo clean
	@rm -rf bin/
	@echo "Clean complete"

# Run example
run-example: build
	@echo "Running flash loan example..."
	@./pipeline.sh < test/fixtures/valid/simple-flash-loan.json | jq .

# Install dependencies
deps:
	@echo "Installing dependencies..."
	@cargo fetch
	@echo "Dependencies installed"

# Format code
fmt:
	@echo "Formatting code..."
	@cargo fmt --all
	@echo "Format complete"

# Check code
check:
	@echo "Checking code..."
	@cargo check --all
	@cargo clippy --all
	@echo "Check complete"

# Show help
help:
	@echo "Atomic Mesh VM Compiler - Build Targets"
	@echo "======================================"
	@echo ""
	@echo "  make build       - Build all compiler components"
	@echo "  make test        - Run all tests"
	@echo "  make clean       - Clean build artifacts"
	@echo "  make run-example - Run flash loan example"
	@echo "  make deps        - Install dependencies"
	@echo "  make fmt         - Format code"
	@echo "  make check       - Run checks and lints"
	@echo "  make help        - Show this help message"
	@echo ""