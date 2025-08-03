/--
Concrete example of atomic cross-chain flash loan using Phase 6 bridge types.
Demonstrates HTLB, zk-SNARK, and threshold signature bridges.
-/

import Bridge.IsoBundle
import Examples.AtomicFlashLoan
import Protocol.Aave.Compile
import Protocol.UniV2.Compile

namespace Examples

open CategoryTheory Grothendieck Stack Bridge

/-- Example HTLB bridge from Polygon to Arbitrum. -/
def polygonToArbitrumHTLB : Bridge :=
  htlbBridge Chain.polygon Chain.arbitrum 5 "0xabc123" 20

/-- Example zk-SNARK bridge for fast finality. -/
def polygonToArbitrumZK : Bridge :=
  zkBridge Chain.polygon Chain.arbitrum 2 "proof_data" ["block_hash", "state_root"]

/-- Example threshold signature bridge. -/
def polygonToArbitrumThreshold : Bridge :=
  thresholdBridge Chain.polygon Chain.arbitrum 3 
    ["sig1", "sig2", "sig3", "sig4", "sig5"] 3

/-- Prove the HTLB bridge is valid. -/
lemma htlb_valid : polygonToArbitrumHTLB.isValid := by
  simp [polygonToArbitrumHTLB, htlbBridge, Bridge.isValid]
  norm_num

/-- Prove the threshold bridge has enough signatures. -/
lemma threshold_valid : polygonToArbitrumThreshold.isValid := by
  simp [polygonToArbitrumThreshold, thresholdBridge, Bridge.isValid]
  norm_num

/-- Complete atomic bundle using HTLB bridges. -/
def htlbFlashLoanBundle : Bundle where
  start := ⟨100, fun _ => Address.default⟩
  finish := ⟨115, fun _ => Address.default⟩  -- 5 + 5 blocks for round trip + 5 for ops
  forward := 
    -- Borrow on Polygon at t=100
    liftMorphism (L := Chain.polygon) (t := 100)
      (Aave.compileToFibre [Aave.Prim.borrow 100]) ≫
    -- Bridge to Arbitrum (arrives at t=105)
    { t_le := by norm_num : 100 ≤ 105, 
      α := fun L => if L = Chain.arbitrum then 𝟙 _ else 𝟙 _ } ≫
    -- Swap on Arbitrum at t=105
    liftMorphism (L := Chain.arbitrum) (t := 105)
      (UniV2.compileToFibre { dx := 100 }) ≫
    -- Bridge back to Polygon (arrives at t=110)
    { t_le := by norm_num : 105 ≤ 110,
      α := fun L => if L = Chain.polygon then 𝟙 _ else 𝟙 _ } ≫
    -- Repay on Polygon at t=110
    liftMorphism (L := Chain.polygon) (t := 110)
      (Aave.compileToFibre [Aave.Prim.repay 100]) ≫
    -- Advance to final time
    { t_le := by norm_num : 110 ≤ 115, α := fun _ => 𝟙 _ }
  repay := id _
  atomicity := by simp

/-- The HTLB bundle satisfies the atomicity checklist. -/
def htlbChecklist : AtomicityChecklist htlbFlashLoanBundle := {
  bridges_invertible := [
    ⟨polygonToArbitrumHTLB, by
      apply htlb_invertible
      norm_num⟩
  ]
  invariants_preserved := by
    intro _; trivial
  state_match := by simp
  time_feasible := by norm_num
}

/-- Therefore the HTLB flash loan is atomic. -/
theorem htlb_flash_loan_atomic : isAtomic htlbFlashLoanBundle := by
  apply checklist_implies_atomic
  exact htlbChecklist

/-- Compare bridge types by their properties. -/
def compareBridges : String :=
  s!"HTLB delay: {polygonToArbitrumHTLB.δ}\n" ++
  s!"ZK delay: {polygonToArbitrumZK.δ}\n" ++
  s!"Threshold delay: {polygonToArbitrumThreshold.δ}\n" ++
  s!"HTLB valid: {polygonToArbitrumHTLB.isValid}\n" ++
  s!"ZK valid: {polygonToArbitrumZK.isValid}\n" ++
  s!"Threshold valid: {polygonToArbitrumThreshold.isValid}"

#eval compareBridges

end Examples 