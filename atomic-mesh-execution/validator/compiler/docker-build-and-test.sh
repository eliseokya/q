#!/bin/bash
# Quick script to build and test the compiler using Docker

set -euo pipefail

echo "=== Atomic Mesh Compiler - Docker Build & Test ==="
echo ""

# Check if docker and docker-compose are available
if ! command -v docker &> /dev/null; then
    echo "❌ Docker is not installed. Please install Docker first."
    exit 1
fi

if ! command -v docker-compose &> /dev/null; then
    echo "❌ Docker Compose is not installed. Please install Docker Compose first."
    exit 1
fi

echo "✅ Docker environment detected"
echo ""

# Build the development image
echo "📦 Building development image..."
docker-compose build dev

echo ""
echo "🔨 Building compiler in release mode..."
docker-compose run --rm build

echo ""
echo "🧪 Running all tests..."
docker-compose run --rm test

echo ""
echo "✅ Build and test completed successfully!"
echo ""
echo "You can now:"
echo "  - Enter dev environment: docker-compose run --rm dev"
echo "  - Run the compiler: docker-compose run --rm compiler"
echo "  - See DOCKER_GUIDE.md for more options"