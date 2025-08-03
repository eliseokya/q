//! Dynamic pattern cache for performance optimization
//!
//! This module provides caching functionality to avoid re-analyzing
//! identical or similar bundles.

use crate::common::{PatternCandidate, Bundle};
use lru::LruCache;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::num::NonZeroUsize;
use std::time::{Duration, Instant};

/// Cache entry with metadata
#[derive(Debug, Clone)]
pub struct CacheEntry {
    pub pattern_match: PatternCandidate,
    pub created_at: Instant,
    pub access_count: u64,
    pub bundle_hash: String,
}

/// Dynamic pattern cache with LRU eviction
pub struct DynamicPatternCache {
    cache: LruCache<String, CacheEntry>,
    max_size: usize,
    ttl: Duration,
    hit_count: u64,
    miss_count: u64,
}

impl DynamicPatternCache {
    /// Create a new cache with specified capacity
    pub fn new(max_size: usize) -> Self {
        Self {
            cache: LruCache::new(NonZeroUsize::new(max_size).unwrap()),
            max_size,
            ttl: Duration::from_secs(3600), // 1 hour default TTL
            hit_count: 0,
            miss_count: 0,
        }
    }

    /// Create cache with custom TTL
    pub fn with_ttl(max_size: usize, ttl: Duration) -> Self {
        Self {
            cache: LruCache::new(NonZeroUsize::new(max_size).unwrap()),
            max_size,
            ttl,
            hit_count: 0,
            miss_count: 0,
        }
    }

    /// Get a cached pattern match
    pub fn get(&mut self, bundle_hash: &str) -> Option<CacheEntry> {
        // First check if expired
        let expired = self.cache.peek(bundle_hash)
            .map(|entry| entry.created_at.elapsed() > self.ttl)
            .unwrap_or(false);
        
        if expired {
            self.cache.pop(bundle_hash);
            self.miss_count += 1;
            return None;
        }
        
        // Now get and clone the entry
        if let Some(entry) = self.cache.get(bundle_hash) {
            self.hit_count += 1;
            Some(entry.clone())
        } else {
            self.miss_count += 1;
            None
        }
    }

    /// Store a pattern match in the cache
    pub fn put(&mut self, bundle_hash: String, pattern_match: PatternCandidate) {
        let entry = CacheEntry {
            pattern_match,
            created_at: Instant::now(),
            access_count: 1,
            bundle_hash: bundle_hash.clone(),
        };

        self.cache.put(bundle_hash, entry);
    }

    /// Compute hash for a bundle
    pub fn compute_bundle_hash(bundle: &Bundle) -> String {
        let mut hasher = DefaultHasher::new();
        bundle.hash(&mut hasher);
        format!("{:x}", hasher.finish())
    }

    /// Get cache statistics
    pub fn get_stats(&self) -> CacheStats {
        let hit_rate = if self.hit_count + self.miss_count > 0 {
            self.hit_count as f64 / (self.hit_count + self.miss_count) as f64
        } else {
            0.0
        };

        CacheStats {
            size: self.cache.len(),
            max_size: self.max_size,
            hit_count: self.hit_count,
            miss_count: self.miss_count,
            hit_rate,
            ttl_seconds: self.ttl.as_secs(),
        }
    }

    /// Clear the cache
    pub fn clear(&mut self) {
        self.cache.clear();
        self.hit_count = 0;
        self.miss_count = 0;
    }

    /// Remove expired entries
    pub fn evict_expired(&mut self) -> usize {
        let mut expired_count = 0;
        let now = Instant::now();

        // Collect expired keys
        let expired_keys: Vec<String> = self.cache
            .iter()
            .filter_map(|(key, entry)| {
                if now.duration_since(entry.created_at) > self.ttl {
                    Some(key.clone())
                } else {
                    None
                }
            })
            .collect();

        // Remove expired entries
        for key in expired_keys {
            if self.cache.pop(&key).is_some() {
                expired_count += 1;
            }
        }

        expired_count
    }
}

#[derive(Debug, Clone)]
pub struct CacheStats {
    pub size: usize,
    pub max_size: usize,
    pub hit_count: u64,
    pub miss_count: u64,
    pub hit_rate: f64,
    pub ttl_seconds: u64,
}

impl Default for DynamicPatternCache {
    fn default() -> Self {
        Self::new(1000) // Default 1000 entry cache
    }
} 