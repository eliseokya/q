# Build stage
FROM rust:1.75-slim as builder

# Install build dependencies
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

# Create app directory
WORKDIR /usr/src/compiler

# Copy workspace Cargo.toml and Cargo.lock (if exists)
COPY Cargo.toml Cargo.lock* ./

# Copy all source code
COPY src ./src

# Build all components in release mode
RUN cargo build --release --all

# Runtime stage
FROM debian:bookworm-slim

# Install runtime dependencies
RUN apt-get update && apt-get install -y \
    libssl3 \
    ca-certificates \
    jq \
    && rm -rf /var/lib/apt/lists/*

# Create non-root user
RUN useradd -m -u 1000 -s /bin/bash compiler

# Create necessary directories
RUN mkdir -p /opt/compiler/bin /opt/compiler/test /opt/compiler/examples \
    && chown -R compiler:compiler /opt/compiler

WORKDIR /opt/compiler

# Copy executables from builder
COPY --from=builder /usr/src/compiler/target/release/parse-and-validate ./bin/
COPY --from=builder /usr/src/compiler/target/release/transform-actions ./bin/
COPY --from=builder /usr/src/compiler/target/release/build-expression ./bin/
COPY --from=builder /usr/src/compiler/target/release/assemble-bundle ./bin/

# Copy pipeline script
COPY pipeline.sh ./
RUN chmod +x pipeline.sh

# Copy test fixtures and examples
COPY test ./test
COPY examples ./examples

# Switch to non-root user
USER compiler

# Set PATH to include bin directory
ENV PATH="/opt/compiler/bin:${PATH}"

# Default command shows help
CMD ["parse-and-validate", "--help"]