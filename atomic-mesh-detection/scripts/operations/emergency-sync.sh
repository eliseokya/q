#!/bin/bash
# Emergency fast sync procedure

set -e

CHAIN=$1
if [ -z "$CHAIN" ]; then
  echo "Usage: $0 <chain>"
  exit 1
fi

echo "Starting emergency sync for $CHAIN..."

# Stop node
node-manager stop --chain=$CHAIN --force

# Download snapshot
echo "Downloading snapshot..."
wget -O /tmp/$CHAIN-snapshot.tar.gz \
  https://snapshots.example.com/$CHAIN-latest.tar.gz

# Extract snapshot
tar -xzf /tmp/$CHAIN-snapshot.tar.gz -C /data/$CHAIN

# Start node
node-manager start --chain=$CHAIN --sync-mode=fast

# Monitor sync
chain-sync-monitor --chain=$CHAIN --continuous

echo "Emergency sync initiated"
