#!/bin/bash
# Initialize databases for all chains

set -e

echo "Initializing databases..."

# Initialize RocksDB for each chain
for chain in ethereum arbitrum polygon base optimism; do
  echo "Initializing $chain database..."
  unified-reth db init \
    --chain=$chain \
    --datadir=/data/$chain \
    --optimize=true
done

# Create indexes for fast queries
unified-reth db create-indexes \
  --chains=all \
  --indexes=address,topic,block

echo "Database initialization complete"
