#!/bin/bash
# Backup node state and detection data

set -e

BACKUP_DIR="/backups/$(date +%Y%m%d_%H%M%S)"
mkdir -p $BACKUP_DIR

echo "Backing up detection system state..."

# Backup node databases
for chain in ethereum arbitrum polygon base optimism; do
  echo "Backing up $chain..."
  unified-reth db backup \
    --chain=$chain \
    --output=$BACKUP_DIR/$chain.db \
    --compress
done

# Backup configurations
cp -r configs $BACKUP_DIR/

# Backup detection state
tar -czf $BACKUP_DIR/detection-state.tar.gz \
  logs/ \
  monitoring/dashboards/

echo "Backup complete: $BACKUP_DIR"
