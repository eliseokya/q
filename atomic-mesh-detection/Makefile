# Makefile for atomic-mesh-detection

.PHONY: all build test install clean

all: build

build:
	@echo "Building unified-reth..."
	cd nodes/unified-reth && cargo build --release
	@echo "Setting up Python tools..."
	pip install -r requirements.txt
	@echo "Making all tools executable..."
	chmod +x nodes/node-tools/* extractors/* analyzers/* detectors/* tools/*

test:
	@echo "Running Rust tests..."
	cd nodes/unified-reth && cargo test
	@echo "Running Python tests..."
	pytest tests/

install: build
	@echo "Installing detection system..."
	mkdir -p /usr/local/atomic-mesh/detection
	cp -r * /usr/local/atomic-mesh/detection/
	@echo "Setting up systemd services..."
	cp scripts/systemd/*.service /etc/systemd/system/
	systemctl daemon-reload

run-nodes:
	./scripts/operations/start-detection.sh

clean:
	cd nodes/unified-reth && cargo clean
	find . -name "*.pyc" -delete
	find . -name "__pycache__" -delete
