# Docker Guide for Atomic Mesh Compiler

This guide explains how to build, test, and run the Atomic Mesh Compiler using Docker.

## Prerequisites

- Docker Engine 20.10+ 
- Docker Compose v2.0+

## Quick Start

### 1. Build the Development Image and Run Tests

```bash
# Build and run all tests
docker-compose run --rm test
```

### 2. Build the Compiler

```bash
# Build all components in release mode
docker-compose run --rm build
```

### 3. Run the Compiler Pipeline

```bash
# Create output directory
mkdir -p output

# Run the compiler on example input
docker-compose run --rm compiler
```

## Available Docker Services

### `dev` - Development Environment

Interactive development environment with full Rust toolchain:

```bash
# Enter development shell
docker-compose run --rm dev

# Inside the container:
cargo build --all          # Build all components
cargo test --all           # Run all tests
cargo test -p parse-and-validate  # Test specific component
make test                  # Run integration tests
```

### `test` - Test Runner

Runs all unit and integration tests:

```bash
docker-compose run --rm test
```

### `build` - Build Only

Builds all components in release mode:

```bash
docker-compose run --rm build
```

### `compiler` - Production Runtime

Runs the compiler pipeline on input files:

```bash
# Run on default example
docker-compose run --rm compiler

# Run on custom input
docker-compose run --rm compiler /opt/compiler/pipeline.sh /data/input/your-file.json
```

## Building Images Manually

### Production Image

```bash
# Build minimal production image
docker build -t atomic-mesh-compiler:latest .

# Run the production image
docker run --rm -v $(pwd)/examples/input:/data/input:ro \
    -v $(pwd)/output:/data/output \
    atomic-mesh-compiler:latest \
    /opt/compiler/pipeline.sh /data/input/flash-loan.json
```

### Development Image

```bash
# Build development image
docker build -f Dockerfile.dev -t atomic-mesh-compiler:dev .

# Run interactive development shell
docker run --rm -it -v $(pwd):/workspace atomic-mesh-compiler:dev
```

## Volume Mounts

- **Production**: 
  - `/data/input` - Input JSON files (read-only)
  - `/data/output` - Output directory for results

- **Development**:
  - `/workspace` - Full source code directory
  - Cargo cache is persisted in named volume

## Environment Variables

- `RUST_LOG` - Log level (error, warn, info, debug, trace)
- `CARGO_TERM_COLOR` - Terminal color output (always, auto, never)
- `RUST_BACKTRACE` - Backtrace on panic (0, 1, full)

## Common Tasks

### Watch for Changes (Development)

```bash
docker-compose run --rm dev cargo watch -x "test --all"
```

### Format Code

```bash
docker-compose run --rm dev cargo fmt --all
```

### Check Code Quality

```bash
docker-compose run --rm dev cargo clippy --all
```

### Clean Build Artifacts

```bash
docker-compose run --rm dev cargo clean
```

### Run Specific Component

```bash
# Inside dev container
./bin/parse-and-validate < examples/input/flash-loan.json
```

## Troubleshooting

### Build Fails

1. Ensure Docker has enough resources (4GB+ RAM recommended)
2. Clear Docker cache: `docker system prune -a`
3. Remove Cargo cache volume: `docker volume rm compiler_cargo-cache`

### Tests Fail

1. Check logs: `docker-compose logs`
2. Run with debug logging: `RUST_LOG=debug docker-compose run --rm test`
3. Run specific test: `docker-compose run --rm dev cargo test test_name`

### Performance Issues

1. Use BuildKit: `DOCKER_BUILDKIT=1 docker-compose build`
2. Increase Docker memory limit
3. Use cargo cache volume (already configured)

## CI/CD Integration

### GitHub Actions Example

```yaml
- name: Build and Test Compiler
  run: |
    docker-compose run --rm build
    docker-compose run --rm test
```

### GitLab CI Example

```yaml
test:
  script:
    - docker-compose run --rm test
```