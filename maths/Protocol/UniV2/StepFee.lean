import Protocol.UniV2.Base
import Protocol.UniV2.Alg.Common
import Protocol.UniV2.Alg.Pos
import Protocol.UniV2.Alg.Product
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Step function with 0.3 % fee (Uniswap V2 default): effective multiplier 997/1000.
-/

namespace UniV2

open Rat

/-- Fee multiplier: 997 / 1000. -/
@[simp] def α : ℚ := 997/1000

@[simp]
def stepFee (a : Action) (p : Pool) : Pool :=
  if h : a.dx = 0 then p else
    let dxFee := α * a.dx
    let x'    := p.x + dxFee
    let dy    := (dxFee * p.y) / x'
    { x := x', y := p.y - dy }

open UniV2.Alg

lemma invariant_fee (a : Action) (p : Pool)
    (hx : 0 < p.x) (h_dx : 0 < a.dx) :
    k (stepFee a p) = k p := by
  have hpos := pos_den (x:=p.x) (dx:=a.dx) hx h_dx
  have hden := ne_zero_den (x:=p.x) (dx:=a.dx) hpos
  have : k (stepFee a p) = (p.x + α * a.dx) * (p.y - (α * a.dx * p.y)/(p.x + α * a.dx)) := by
    by_cases hdx0 : a.dx = 0
    · have : (a.dx : ℚ) = 0 := by exact_mod_cast hdx0
      have : (α : ℚ) * a.dx = 0 := by
        simp [this]
      simp [stepFee, hdx0, k] at *
    · simp [stepFee, hdx0, k]
  simpa [this] using
    const_prod (x:=p.x) (y:=p.y) (dx:=a.dx) hden

end UniV2 