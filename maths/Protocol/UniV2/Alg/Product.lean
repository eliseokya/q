import UniV2.Alg.Common
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace UniV2.Alg
open Rat

lemma const_prod (x y dx : ℚ) (hden : x + α*dx ≠ 0) :
    (x + α*dx)*(y - (α*dx*y)/(x + α*dx)) = x*y := by
  field_simp [hden, α] ; ring

end UniV2.Alg 