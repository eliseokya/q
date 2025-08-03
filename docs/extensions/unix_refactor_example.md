# Unix-Style Refactor: Concrete Implementation

## Current vs. Unix-Style Architecture

### **Current Monolithic Approach**
```lean
-- Everything in one verification function
def verify_bundle (verifier : BundleVerifier) (submission : BundleSubmission) : 
    IO VerificationResult := do
  -- Step 1: Type checking
  match typeCheck submission.bundle with
  -- Step 2: Gas estimation  
  -- Step 3: Compilation
  -- Step 4: Security verification
  -- Step 5: Proof generation
```

### **Unix-Style Decomposition**
```bash
# Each step becomes an independent service
cat bundle.dsl | typecheck | gasestimate | compile | verify | execute
```

---

## Concrete Service Decomposition

### **1. Type Checker Service**
```lean
-- maths/services/TypeChecker.lean
namespace TypeChecker

structure Input where
  bundle : DSL.Bundle
  deriving ToJson, FromJson

structure Output where  
  result : Except TypeError DSL.State
  diagnostics : List String
  deriving ToJson, FromJson

-- Pure mathematical specification
def pure_typecheck (input : Input) : Output :=
  { result := DSL.typeCheck input.bundle
    diagnostics := [] }

-- Implementation with caching/optimization
def cached_typecheck (cache : StateT (HashMap String Output) IO) 
    (input : Input) : IO Output := do
  let key := hash input.bundle.name
  match (← get).get? key with
  | some cached => return cached
  | none => 
      let result := pure_typecheck input
      modify (·.insert key result)
      return result

end TypeChecker
```

### **2. Compilation Service**
```lean
-- maths/services/Compiler.lean
namespace Compiler

structure Input where
  bundle : DSL.Bundle
  typecheck_result : DSL.State
  deriving ToJson, FromJson

structure Output where
  lean_code : String
  morphism_data : String  -- Serialized bicategory morphism
  proof_obligations : List String
  deriving ToJson, FromJson

-- Pure specification
def pure_compile (input : Input) : Output :=
  match DSL.compile input.bundle with
  | Except.ok compiled => 
      { lean_code := DSL.generateLeanCode input.bundle
        morphism_data := serialize compiled.morphism
        proof_obligations := extract_obligations compiled }
  | Except.error e =>
      { lean_code := s!"-- Error: {e}"
        morphism_data := ""
        proof_obligations := [] }

end Compiler
```

### **3. Bridge Verifier Service**
```lean
-- maths/services/BridgeVerifier.lean
namespace BridgeVerifier

structure Input where
  bridges : List Bridge.Bridge
  security_level : ℕ
  deriving ToJson, FromJson

structure Output where
  valid : Bool
  invertibility_proofs : List String
  security_analysis : String
  deriving ToJson, FromJson

-- Distributed verification across multiple nodes
def distributed_verify (nodes : List Node) (input : Input) : IO Output := do
  let tasks := input.bridges.map (verify_single_bridge · input.security_level)
  let results ← tasks.mapM (distribute_to_node nodes)
  return aggregate_results results

end BridgeVerifier
```

---

## Stream Processing Implementation

### **Pipeline Orchestrator**
```lean
-- maths/services/Pipeline.lean
namespace Pipeline

-- Unix-style pipeline with proper error handling
def verification_pipeline (bundle_json : String) : IO String := do
  -- Parse input
  let bundle ← parse_bundle bundle_json
  
  -- Stage 1: Type checking
  let typecheck_out ← run_service "typecheck" (serialize bundle)
  if typecheck_out.failed then
    return error_response "Type checking failed" typecheck_out.stderr
  
  -- Stage 2: Compilation  
  let compile_out ← run_service "compile" typecheck_out.stdout
  if compile_out.failed then
    return error_response "Compilation failed" compile_out.stderr
    
  -- Stage 3: Verification
  let verify_out ← run_service "verify" compile_out.stdout
  if verify_out.failed then
    return error_response "Verification failed" verify_out.stderr
    
  return verify_out.stdout

-- Run service with timeout and resource limits
def run_service (name : String) (input : String) : IO ProcessResult := do
  let proc ← Process.spawn {
    cmd := s!"./services/{name}"
    stdin := .piped
    stdout := .piped  
    stderr := .piped
  }
  proc.stdin.write input
  proc.stdin.close
  let result ← proc.wait
  return { 
    stdout := (← proc.stdout.readToEnd)
    stderr := (← proc.stderr.readToEnd)
    exit_code := result
    failed := result ≠ 0
  }

end Pipeline
```

---

## Incremental Verification

### **Dependency Tracking**
```lean
-- maths/services/IncVerifier.lean
namespace IncVerifier

-- Track dependencies between bundle components
structure BundleDependency where
  component : String
  depends_on : List String
  hash : String  -- Content hash for change detection
  last_verified : Option Timestamp

-- Only reverify changed components and their dependents
def incremental_verify (old_deps : List BundleDependency) 
    (new_bundle : DSL.Bundle) : IO VerificationPatch := do
  let new_deps := extract_dependencies new_bundle
  let changed := find_changes old_deps new_deps
  let to_verify := compute_transitive_dependents changed new_deps
  
  -- Verify only the changed components
  let results ← to_verify.mapM verify_component
  return VerificationPatch.mk results

-- Categorical model: dependencies form a DAG
theorem dependency_acyclic (deps : List BundleDependency) :
  IsDAG (dep_relation deps) := by
  -- Proof that our dependency extraction creates acyclic graphs
  sorry

end IncVerifier
```

---

## Caching with Correctness Guarantees

### **Cached Verification**
```lean
-- maths/services/Cache.lean
namespace Cache

-- Cache with mathematical correctness guarantee
structure VerificationCache where
  store : HashMap String CachedResult
  coherence : ∀ k v, store.get? k = some v → v.result = pure_verify v.input

-- Cache operations preserve correctness
theorem cache_correctness (cache : VerificationCache) (key : String) :
  ∀ result, cache.get key = some result → 
  result.output = pure_verify result.input := by
  intro result h
  exact cache.coherence key result h

-- Incremental cache update
def update_cache (cache : VerificationCache) (key : String) 
    (input : VerificationInput) : IO VerificationCache := do
  let result ← compute_verification input
  return { cache with 
    store := cache.store.insert key { input, result }
    coherence := extend_coherence cache.coherence key result }

end Cache
```

---

## Performance Monitoring Per Service

### **Service Metrics**
```lean
-- maths/services/Metrics.lean
namespace Metrics

structure ServiceMetrics where
  service_name : String
  request_count : ℕ
  average_latency : ℚ  -- milliseconds
  error_rate : ℚ       -- percentage
  throughput : ℚ       -- requests/second
  memory_usage : ℕ     -- MB

-- Monitor each service independently
def collect_metrics (service : String) : IO ServiceMetrics := do
  let stats ← read_service_stats service
  return {
    service_name := service
    request_count := stats.total_requests
    average_latency := stats.total_time / stats.total_requests
    error_rate := stats.errors / stats.total_requests * 100
    throughput := stats.total_requests / stats.uptime_seconds
    memory_usage := stats.memory_mb
  }

-- Alert on performance degradation
def check_service_health (metrics : ServiceMetrics) : List Alert :=
  let mut alerts := []
  if metrics.average_latency > 1000 then  -- > 1 second
    alerts := Alert.slow_service metrics.service_name metrics.average_latency :: alerts
  if metrics.error_rate > 5 then  -- > 5% errors
    alerts := Alert.high_errors metrics.service_name metrics.error_rate :: alerts
  alerts

end Metrics
```

---

## Benefits Achieved

### **1. Independent Scaling**
```bash
# Scale bottleneck services independently
docker-compose scale typecheck=1 compile=3 verify=2 execute=1
```

### **2. Fault Isolation**
```bash
# If one service fails, others continue
if ! typecheck < bundle.dsl; then
  echo "Type checking failed, but other services still healthy"
  exit 1
fi
```

### **3. Easy Testing**
```bash
# Test each component in isolation
echo '{"bundle": {...}}' | typecheck | jq '.result'
echo '{"bridges": [...]}' | bridge-verifier | jq '.valid'
```

### **4. Performance Optimization Without Mathematical Changes**
```bash
# A/B test different implementations
cat bundle.dsl | typecheck-fast   # New optimized version
cat bundle.dsl | typecheck-slow   # Original reference implementation
# Both produce identical mathematical results
```

### **5. Horizontal Distribution**
```bash
# Distribute across multiple machines
cat bundle.dsl | ssh node1 typecheck | ssh node2 compile | ssh node3 verify
```

---

## Implementation Timeline

### **Phase 1: Service Extraction** (2 weeks)
- Extract type checker as standalone service
- Extract compiler as standalone service  
- Implement JSON communication protocol

### **Phase 2: Pipeline Integration** (1 week)
- Build pipeline orchestrator
- Add proper error handling and timeouts
- Performance benchmarking

### **Phase 3: Caching & Optimization** (2 weeks)
- Implement verification cache with correctness proofs
- Add incremental verification
- Performance monitoring per service

### **Phase 4: Distribution** (2 weeks)
- Containerize all services
- Implement distributed verification
- Load balancing and auto-scaling

The key insight: **Each service does one mathematical operation perfectly, but can be implemented and optimized independently.** 