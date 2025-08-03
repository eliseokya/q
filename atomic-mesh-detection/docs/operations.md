# Operations Guide

## Starting the System
```bash
./scripts/operations/start-detection.sh
```

## Monitoring
- Grafana: http://localhost:3000
- Prometheus: http://localhost:9090
- Logs: /var/log/detection/

## Maintenance

### Node Updates
```bash
./scripts/operations/update-nodes.sh
```

### Backup
```bash
./scripts/operations/backup-state.sh
```

### Emergency Procedures
```bash
./scripts/operations/emergency-sync.sh <chain>
```

## Troubleshooting

### Node Sync Issues
1. Check peer connectivity
2. Verify disk space
3. Review node logs

### Detection Issues
1. Check latency metrics
2. Verify integration status
3. Review strategy logs
