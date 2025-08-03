import UniV2.Alg.Common
import Mathlib.Tactic.Linarith

namespace UniV2.Alg
open Rat

lemma pos_den {x dx : ℚ} (hx : 0 < x) (hdx : 0 < dx) :
    0 < x + α * dx := by
  have hα : 0 < α := alpha_pos
  have : 0 < α * dx := mul_pos hα hdx
  have : 0 < x + α * dx := add_pos hx this
  simpa using this

lemma ne_zero_den {x dx : ℚ} (h : 0 < x + α * dx) :
    x + α * dx ≠ 0 := (ne_of_gt h)

end UniV2.Alg 