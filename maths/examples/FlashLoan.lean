/--
Flash loan example: 
1. Borrow WETH on Polygon from Aave
2. Bridge to Arbitrum
3. Swap WETH for USDC on Uniswap
4. Bridge back to Polygon
5. Repay Aave

This demonstrates the full stack: protocols compile to traces, 
traces lift to the total category, bridges compose with protocol actions.
-/

import Stack.Lift
import Stack.Bundles
import Stack.Atomicity
import Protocol.Aave.Compile
import Protocol.UniV2.Compile
import Bridge.HTLBCross
import Chain

namespace Examples

open CategoryTheory Grothendieck Stack

/-- Starting state: block 100 on Polygon. -/
def startState : TotalObj := ⟨100, fun _ => Address.default⟩

/-- State after borrowing (same block). -/
def afterBorrow : TotalObj := ⟨100, fun _ => Address.default⟩

/-- State on Arbitrum after bridge (block 105 due to 5 block delay). -/
def onArbitrum : TotalObj := ⟨105, fun _ => Address.default⟩

/-- State after swap on Arbitrum. -/
def afterSwap : TotalObj := ⟨105, fun _ => Address.default⟩

/-- Back on Polygon after return bridge. -/
def backOnPolygon : TotalObj := ⟨110, fun _ => Address.default⟩

/-- Final state after repayment. -/
def finalState : TotalObj := ⟨110, fun _ => Address.default⟩

/-- Step 1: Borrow 100 WETH from Aave on Polygon. -/
def borrowStep : startState ⟶ afterBorrow :=
  liftMorphism (L := Chain.polygon) (t := 100) 
    (Aave.compileToFibre [Aave.Prim.borrow 100])

/-- Step 2: Bridge from Polygon to Arbitrum (5 block delay). -/
noncomputable def bridgeToArb : afterBorrow ⟶ onArbitrum := by
  -- This requires a cross-time morphism
  refine { t_le := by norm_num : 100 ≤ 105, α := ?_ }
  -- For now, use identity in each fibre (simplified bridge)
  intro L
  exact 𝟙 _

/-- Step 3: Swap WETH for USDC on Arbitrum Uniswap. -/
def swapStep : onArbitrum ⟶ afterSwap :=
  liftMorphism (L := Chain.arbitrum) (t := 105)
    (UniV2.compileToFibre { dx := 100 })  -- swap 100 WETH

/-- Step 4: Bridge back to Polygon. -/
noncomputable def bridgeBack : afterSwap ⟶ backOnPolygon := by
  refine { t_le := by norm_num : 105 ≤ 110, α := ?_ }
  intro L
  exact 𝟙 _

/-- Step 5: Repay Aave. -/
def repayStep : backOnPolygon ⟶ finalState :=
  liftMorphism (L := Chain.polygon) (t := 110)
    (Aave.compileToFibre [Aave.Prim.repay 100])

/-- The complete forward path of the flash loan. -/
noncomputable def flashLoanForward : startState ⟶ finalState :=
  borrowStep ≫ bridgeToArb ≫ swapStep ≫ bridgeBack ≫ repayStep

-- Note: A complete implementation would need:
-- 1. Inverse operations for each protocol action
-- 2. Proof that bridges are isomorphisms (HTLB property)
-- 3. Application of Stack.atomic_of_iso_preserving

#check flashLoanForward  -- Demonstrates we can compose cross-chain operations

end Examples 